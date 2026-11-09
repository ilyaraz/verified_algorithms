import DataStructures.PerfectHash.Source.Search.Model

namespace PerfectHash.Source
open WordRam RamLang RamLang.Compiler

/-- Application scratch occupies only the prefix preceding the internal stack. -/
def workspace (l : Layout) (N : Nat) : Region := ⟨l.scratchBase,6*(N+1)⟩

/-- The source algorithm may use input, output and the small scratch prefix.
Compiler stack accesses are accounted separately and then included publicly. -/
def policy (w N : Nat) (l : Layout) : AccessPolicy w :=
  ⟨fun a => (l.input N).Contains a ∨ (l.output N).Contains a ∨ (workspace l N).Contains a,
   fun a => (l.output N).Contains a ∨ (workspace l N).Contains a,(l.random w N).Contains⟩

/-- Small application scratch is a subregion of the original reservation. -/
theorem workspace_inside (h : (workspace l N).Contains (a : Addr w)) : (l.scratch N).Contains a := by
  simp only [workspace,Layout.scratch,workspaceCapacity,Region.Contains] at h ⊢
  omega

/-- Every source ordinary access is separated from the internally placed stack. -/
theorem separated (ha : Admissible w N l) (hp : (policy w N l).AllowsTrace log) :
    RamLang.Compiler.Separated (Entry.stack l N) log := by
  have outside (a : Addr w) (h : (policy w N l).read a) : ¬ (Entry.stack l N).Contains a := by
    intro hs
    rcases h with hi | ho | hwork
    · exact Region.not_contains_of_separated ha.ordinary.input_scratch hi (Entry.stack_inside hs)
    · exact Region.not_contains_of_separated ha.ordinary.output_scratch ho (Entry.stack_inside hs)
    · exact Region.not_contains_of_separated (Entry.stack_separated l N) hwork hs
  intro e he
  have h := hp e he
  cases e with
  | randomRead => rfl
  | dataRead a v =>
    have hout := outside a h
    simp [RamLang.ABI.applicationEvent]
    unfold Region.Contains at hout
    omega
  | dataWrite a v =>
    have hout := outside a (Or.inr h)
    simp [RamLang.ABI.applicationEvent]
    unfold Region.Contains at hout
    omega

/-- After adding the physical stack trace, all accesses still obey the original
public memory reservations and random-address policy. -/
theorem public_policy (h : (RamLang.Compiler.withStack (Entry.stack l N) (policy w N l)).AllowsTrace log) :
    (PerfectHash.Bounded.policy w N l).AllowsTrace log := by
  intro e he
  have hh := h e he
  cases e with
  | randomRead => exact hh
  | dataRead a v =>
    rcases hh with hs | hi | ho | hw
    · exact Or.inr (Or.inr (Entry.stack_inside hs))
    · exact Or.inl hi
    · exact Or.inr (Or.inl ho)
    · exact Or.inr (Or.inr (workspace_inside hw))
  | dataWrite a v =>
    rcases hh with hs | ho | hw
    · exact Or.inr (Entry.stack_inside hs)
    · exact Or.inl ho
    · exact Or.inr (workspace_inside hw)

/-- Source deduplication has exactly the small workspace policy. -/
theorem dedup_policy {w N : Nat} {l : Layout} {log : List (Access w)} (h : (Dedup.Source.Pass.policy (PerfectHash.Bounded.dedupLayout l) N).AllowsTrace log) :
    (policy w N l).AllowsTrace log := by
  intro e he
  have hh := h e he
  cases e with
  | dataRead => rcases hh with hi | hs; exact Or.inl hi; exact Or.inr (Or.inr hs)
  | dataWrite => exact Or.inr hh
  | randomRead => exact False.elim hh

/-- A header address belongs to the caller's fitting output reservation. -/
theorem header_inside (ha : Admissible w N l) (hi : i < 4) : (l.output N).Contains (word w (l.outputBase+i)) :=
  Region.contains_index ha.ordinary.output (by change i < 64*(N+1); omega)

/-- Root trials use the compact input and nodes entirely below the stack. -/
theorem root_policy (xs : List (Word w)) (l : Layout)
    (h : (Source.Root.policy (Region.mk ((PerfectHash.Bounded.dedupLayout l).compact xs.length).base
      (PerfectHash.Bounded.values xs).length)
      (l.outputBase+4) l.scratchBase (PerfectHash.Bounded.rootSlots xs) (PerfectHash.Bounded.values xs).length).AllowsTrace log) :
    (policy w xs.length l).AllowsTrace log := by
  have hd := PerfectHash.Bounded.values_length_le xs
  have hm := PerfectHash.Bounded.root_slots_bound xs
  intro e he
  have hh := h e he
  cases e with
  | dataRead a v =>
    change _ ∨ _ at hh
    simp only [PerfectHash.Bounded.dedupLayout,Dedup.Layout.compact,Region.Contains] at hh
    change _ ∨ _ ∨ _
    simp only [Layout.input,Layout.output,dictionaryCapacity,workspace,Region.Contains]
    rcases hh with hh | hh <;> omega
  | dataWrite a v =>
    change _ ∨ _ at hh
    simp only [Region.Contains] at hh
    change _ ∨ _
    simp only [Layout.output,dictionaryCapacity,workspace,Region.Contains]
    rcases hh with hh | hh <;> omega
  | randomRead => exact False.elim hh

/-- A child's linked nodes lie in scratch and its private slots in retained
output; both remain separated from the compiler's stack suffix. -/
theorem child_policy (ha : Admissible w xs.length l) (hy : PerfectHash.Bounded.rootAccepted xs a = true)
    (b : Fin (PerfectHash.Bounded.rootSlots xs))
    (h : (Source.Child.policy l.scratchBase (PerfectHash.Bounded.values xs).length
      (Packed.table l.outputBase (PerfectHash.Bounded.childCapacity xs a) b)
      (PerfectHash.Bounded.childCapacity xs a b)).AllowsTrace log) :
    (policy w xs.length l).AllowsTrace log := by
  have hd := PerfectHash.Bounded.values_length_le xs
  have hq := PerfectHash.Bounded.retained_bound hy
  have hb := Packed.prefix_bound (PerfectHash.Bounded.childCapacity xs a) b
  intro e he
  have hh := h e he
  cases e with
  | dataRead addr v =>
    change _ ∨ _ at hh
    simp only [Region.Contains,Packed.table,Packed.tablesBase] at hh
    change _ ∨ _ ∨ _
    simp only [Layout.input,Layout.output,dictionaryCapacity,workspace,Region.Contains]
    unfold Packed.words at hq
    rcases hh with hh | hh <;> omega
  | dataWrite addr v =>
    change (Region.mk _ _).Contains addr at hh
    simp only [Region.Contains,Packed.table,Packed.tablesBase] at hh
    change _ ∨ _
    simp only [Layout.output,dictionaryCapacity,workspace,Region.Contains]
    unfold Packed.words at hq
    omega
  | randomRead => exact False.elim hh

end PerfectHash.Source
