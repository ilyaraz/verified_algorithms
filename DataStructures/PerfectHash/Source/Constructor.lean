import DataStructures.PerfectHash.Source.Prepare
import DataStructures.PerfectHash.Source.Empty
import DataStructures.PerfectHash.Source.Header
import DataStructures.PerfectHash.Source.RootSpec

namespace PerfectHash.Source.Constructor
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Bounded
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- Public construction parameters are exactly the original nine words. -/
def arguments (w N : Nat) (l : Layout) : List (Word w) :=
  [word w l.inputBase,word w N,word w l.outputBase,word w (dictionaryCapacity N),
   word w l.scratchBase,word w (workspaceCapacity N),word w l.randomBase,
   word w (randomCapacity w N),word w w]

/-- Ordinary failure identifies an exhausted root block or a reached child block. -/
def Failed (root : Option (Word w)) (child : Word w → Fin m → Option (Word w)) : Prop :=
  root = none ∨ ∃ a, root = some a ∧ ∃ b, child a b = none

/-- Successful source output exposes only the retained region and set. The
endpoint result lets the charged public wrapper compute the retained length. -/
def Success (xs : List (Word w)) (l : Layout) (value : Word w) (mem : DataMemory w) : Prop :=
  ∃ r, r.base = l.outputBase ∧ value = word w (r.base+r.size) ∧
    Table.representation.Holds xs.toFinset r mem ∧ r.size ≤ 64*(xs.toFinset.card+1)

/-- Pointwise child work sums every directory entry after an accepted root. -/
def childWork (xs : List (Word w)) (root : Option (Word w))
    (cost : Word w → Fin (rootSlots xs) → Nat) : Nat :=
  match root with | none => 0 | some a => Children.remainingWork xs a (cost a) 0+30

/-- Actual lowered instruction allowances compose preparation, rounding,
searches and orchestration. The empty branch has a separate constant bound. -/
def work (xs : List (Word w)) (l : Layout) (ha : Admissible w xs.length l) (rho : RandomMemory w)
    (root : Option (Word w)) (rootCost : Nat) (cost : Word w → Fin (rootSlots xs) → Nat) : Nat :=
  if xs.length = 0 then 500 else Prepare.work xs l ha rho+19*Hashing.PowerOfTwo.bits (values xs).length+
    rootCost+childWork xs root cost+1000

/-- The empty input path executes the ordinary helper, producing a complete
retained descriptor with no sampling and seventeen additional live stack words. -/
theorem empty_contract {w free : Nat} (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (l : Layout) (ha : Admissible w 0 l) (hfill : p.functions[2]? = some Fill.function)
    (hempty : p.functions[14]? = some Empty.function) (hfree : 17 ≤ free) :
    Contract p rho free Bounded.function.body
      ((arguments w 0 l).map some ++ List.replicate Bounded.function.locals.length none) mem
      (fun flow mem' log => ∃ value, flow = .returned value ∧ Success ([] : List (Word w)) l value mem' ∧
        (Source.policy w 0 l).AllowsTrace log ∧ RamLang.Library.Retry.randomAddresses log = []) 500 17 := by
  obtain ⟨flow,mem',log,d,⟨hf,harray,hp,hr⟩,ht,hs⟩ :=
    Empty.contract (free := free-12) p rho mem l ha hfill (by omega)
  subst flow
  have hspace : 12 ≤ free := by omega
  have hfit : l.outputBase+8 < modulus w := by have h := ha.ordinary.output; change l.outputBase+64 < modulus w at h; omega
  have hview := Empty.representation hfit ha.arithmetic.widthValue harray
  refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
  · exact ⟨_,rfl,⟨⟨l.outputBase,8⟩,rfl,rfl,⟨Empty.data w,hview⟩,by simp⟩,by simpa using hp,by simpa using hr⟩
  · ram_cost
    omega
  · ram_cost
    change 12+extraStack d ≤ 17
    omega

/-- Complete nonempty source construction, parametrized by proved capped or
fallback search contracts. The shared orchestration has no seed advice input. -/
theorem nonempty_contract {w free : Nat} (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (xs : List (Word w)) (l : Layout) (ha : Admissible w xs.length l) (hne : 0 < xs.length)
    (f g : RamLang.Function) (root : Option (Word w)) (rootCost : Nat)
    (child : Word w → Fin (rootSlots xs) → Option (Word w)) (cost : Word w → Fin (rootSlots xs) → Nat)
    (rs : RootSpec p rho xs l f root rootCost)
    (cs : ∀ a, rootAccepted xs a = true → Children.SearchSpec p rho xs l a g (child a) (cost a))
    (hround : p.functions[1]? = some Hashing.Source.Rounding.function)
    (hfill : p.functions[2]? = some Fill.function)
    (hsample : p.functions[3]? = some Hashing.Source.Sampling.function)
    (hfind : p.functions[4]? = some Dedup.Source.Search.function)
    (hdedup : p.functions[5]? = some Dedup.Source.Pass.function)
    (hallocate : p.functions[8]? = some Allocation.function)
    (hchildren : p.functions[11]? = some Children.function)
    (hprepare : p.functions[13]? = some Prepare.function)
    (hfree : 58 ≤ free) (hinput : ArrayAt mem l.inputBase xs) :
    Contract p rho free Bounded.function.body
      ((arguments w xs.length l).map some ++ List.replicate Bounded.function.locals.length none) mem
      (fun flow mem' log => ∃ value, flow = .returned value ∧
        ((value = word w 0 ∧ Failed root child) ∨ Success xs l value mem') ∧
        (Source.policy w xs.length l).AllowsTrace log ∧
        (RamLang.Library.Retry.randomAddresses log).Sublist
          (consecutiveAddresses w l.randomBase (1+w*(rootSlots xs+1))))
      (work xs l ha rho root rootCost cost) 58 := by
  have hnfit : xs.length < modulus w := by have h := ha.arithmetic.linearSizes; omega
  have hnzero : word w xs.length ≠ word w 0 := by
    intro h
    have hh := (word_eq_iff_of_lt hnfit (by omega : 0 < modulus w)).mp h
    omega
  obtain ⟨flow,mem₁,log₁,prepare,⟨hf₁,harray,hp₁,hr₁⟩,ht₁,hs₁⟩ :=
    Prepare.contract (free := free-14) p rho mem xs l ha hround hfill hsample hfind hdedup (by omega) hinput
  subst flow
  let shiftCell := word w l.outputBase+word w 1
  have hmfit : Hashing.PowerOfTwo.size (values xs).length < modulus w := by
    have hm := root_slots_bound xs
    have hd := values_length_le xs
    have hl := ha.arithmetic.linearSizes
    simpa only [rootSlots,Hashing.PowerOfTwo.computeSize_eq] using (show rootSlots xs < modulus w by omega)
  obtain ⟨flow,mem₂,log₂,round,⟨hf₂,hm₂,hl₂⟩,ht₂,hs₂⟩ :=
    Hashing.Source.Rounding.contract (free := free-6) p rho mem₁ (values xs).length shiftCell hmfit
  subst flow
  subst mem₂
  subst log₂
  let rounded := update mem₁ shiftCell (word w (w-Hashing.PowerOfTwo.bits (values xs).length))
  have hcell : (l.output xs.length).Contains shiftCell := by
    simpa [shiftCell,WordRam.word_add] using Source.header_inside ha (by decide : 1 < 4)
  have harray' : ArrayAt rounded ((dedupLayout l).compact xs.length).base (values xs) := by
    apply harray.update_outside (rootContext xs l ha).input_fit
    apply Region.not_contains_of_separated (s := ⟨((dedupLayout l).compact xs.length).base,(values xs).length⟩) ?_ hcell
    have hsep := ha.ordinary.output_scratch
    have hd := values_length_le xs
    simp only [Region.Separated,Layout.output,Layout.scratch,dictionaryCapacity,workspaceCapacity] at hsep
    simp only [Region.Separated,dedupLayout,Dedup.Layout.compact,Layout.output,dictionaryCapacity]
    omega
  have rootFree : 34 ≤ free-f.frameSize := by have h := rs.frame; omega
  have hc := rs.body (free-f.frameSize) rounded rootFree harray'
  have hc' : Contract p rho (free-f.frameSize) f.body
      ([word w l.scratchBase+word w 4*word w xs.length+word w 2,word w (values xs).length,
        word w l.outputBase+word w 4,word w l.scratchBase,word w (Hashing.PowerOfTwo.size (values xs).length),
        rounded shiftCell,word w l.randomBase+word w 1,word w w].map some ++ List.replicate f.locals.length none) rounded
      (fun flow mem' log => flow = .returned (root.getD (word w 0)) ∧
        (∀ seed, root = some seed → rootAccepted xs seed = true ∧
          Construction.Grouped (rootHash xs seed) (l.outputBase+4) l.scratchBase (values xs).reverse mem') ∧
        (Source.policy w xs.length l).AllowsTrace log ∧
        (RamLang.Library.Retry.randomAddresses log).Sublist (consecutiveAddresses w (l.randomBase+1) w)) rootCost 34 := by
    have hadd : l.scratchBase+2*(xs.length+1)+2*xs.length = l.scratchBase+4*xs.length+2 := by omega
    simpa [WordRam.word_add,WordRam.word_mul,rounded,update_same,dedupLayout,Dedup.Layout.compact,hadd,
      rootSlots,Hashing.PowerOfTwo.computeSize_eq] using hc
  obtain ⟨flow,mem₃,log₃,search,⟨hf₃,hgroup,hp₃,hr₃⟩,ht₃,hs₃⟩ := hc'
  subst flow
  have hlookup := rs.lookup
  have hparams := rs.parameters
  have hfspace : f.frameSize ≤ free := by have h := rs.frame; omega
  have hprepareSpace : 14 ≤ free := by omega
  have hroundSpace : 6 ≤ free := by omega
  have hchildrenSpace : 18 ≤ free := by omega
  have hschedule : consecutiveAddresses w l.randomBase (1+w*(rootSlots xs+1)) =
      [word w l.randomBase] ++ consecutiveAddresses w (l.randomBase+1) w ++
        consecutiveAddresses w (childRandomBase l w 0) (w*rootSlots xs) := by
    rw [show 1+w*(rootSlots xs+1) = 1+w+w*rootSlots xs by ring,
      consecutiveAddresses_append,consecutiveAddresses_append]
    simp [consecutiveAddresses,childRandomBase,Nat.add_assoc]
  cases he : root with
  | none =>
    refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · refine ⟨_,rfl,Or.inl ⟨rfl,Or.inl rfl⟩,?_,?_⟩
      · intro e hev
        simp only [Option.toList_none,Option.toList_some,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,false_or] at hev
        rcases hev with hev | rfl | rfl | hev
        · exact hp₁ e hev
        · exact Or.inl hcell
        · exact Or.inr (Or.inl hcell)
        · exact hp₃ e hev
      · simp only [RamLang.Library.Retry.randomAddresses_append,hr₁,hschedule]
        simpa [RamLang.Library.Retry.randomAddresses,Access.randomAddress] using
          ((List.Sublist.refl [word w l.randomBase]).append hr₃).trans (List.sublist_append_left _ _)
    · ram_cost
      simp only [work,childWork,he,if_neg (by omega : xs.length ≠ 0)]
      omega
    · ram_cost
      change 14+extraStack prepare ≤ 58 ∧ 6+extraStack round ≤ 58 ∧ f.frameSize+extraStack search ≤ 58
      have h := rs.frame
      omega
  | some a =>
    have hseed := rs.nonzero a he
    obtain ⟨hy,hg⟩ := hgroup a he
    let header := writeHeader mem₃ l.outputBase a (word w (w-Hashing.PowerOfTwo.bits (values xs).length))
      (word w (rootSlots xs)) (word w (values xs).length)
    have hpart : Partial xs l a 0 header := header_partial ha hy hg
    have hc := Children.contract (free := free-18) ha (cs a hy) hround hallocate (by omega) header hpart
    have hc' : Contract p rho (free-18) Children.function.body
        ([word w l.outputBase+word w 4,word w l.scratchBase,word w (Hashing.PowerOfTwo.size (values xs).length),
          word w l.randomBase+word w 1+word w w,word w w].map some ++ List.replicate Children.function.locals.length none)
        (update (update (update (update mem₃ (word w l.outputBase) (root.getD (word w 0)))
          (word w l.outputBase+word w 1) (rounded shiftCell))
          (word w l.outputBase+word w 2) (word w (Hashing.PowerOfTwo.size (values xs).length)))
          (word w l.outputBase+word w 3) (word w (values xs).length))
        (fun flow mem' log =>
          ((flow = .returned (word w 0) ∧ ∃ b, child a b = none) ∨
            (flow = .returned (word w (l.outputBase+Packed.words (childCapacity xs a))) ∧
              Partial xs l a (rootSlots xs) mem')) ∧ (Source.policy w xs.length l).AllowsTrace log ∧
          (RamLang.Library.Retry.randomAddresses log).Sublist
            (consecutiveAddresses w (childRandomBase l w 0) (w*rootSlots xs)))
        (Children.remainingWork xs a (cost a) 0+30) 40 := by
      simpa [he,WordRam.word_add,rootSlots,Hashing.PowerOfTwo.computeSize_eq,childRandomBase,header,writeHeader,rounded,update_same] using hc
    obtain ⟨flow,mem₄,log₄,children,⟨hq₄,hp₄,hr₄⟩,ht₄,hs₄⟩ := hc'
    have hresult : ∃ value, flow = .returned value ∧
        ((value = word w 0 ∧ Failed root child) ∨ Success xs l value mem₄) := by
      rcases hq₄ with ⟨hf,hfail⟩ | ⟨hf,hcomplete⟩
      · exact ⟨_,hf,Or.inl ⟨rfl,Or.inr ⟨a,he,hfail⟩⟩⟩
      · refine ⟨_,hf,Or.inr ⟨Packed.region l.outputBase (childCapacity xs a),rfl,rfl,
          hcomplete.representation ha,?_⟩⟩
        simpa [Packed.region,values_length,StaticSet.distinctCount] using retained_bound hy
    obtain ⟨value,rfl,hresult⟩ := hresult
    refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · refine ⟨value,rfl,by simpa only [he] using hresult,?_,?_⟩
      · intro e hev
        simp only [Option.toList_none,Option.toList_some,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,false_or] at hev
        rcases hev with hev | rfl | rfl | hev | rfl | rfl | rfl | rfl | hev
        · exact hp₁ e hev
        · exact Or.inl hcell
        · exact Or.inr (Or.inl hcell)
        · exact hp₃ e hev
        · exact Or.inl (by simpa using Source.header_inside ha (i := 0) (by decide))
        · exact Or.inl hcell
        · apply Or.inl; simpa only [Binary.eval,WordRam.word_add] using Source.header_inside ha (by decide : 2 < 4)
        · apply Or.inl; simpa only [Binary.eval,WordRam.word_add] using Source.header_inside ha (by decide : 3 < 4)
        · exact hp₄ e hev
      · simp only [RamLang.Library.Retry.randomAddresses_append,hr₁,hschedule]
        simpa [RamLang.Library.Retry.randomAddresses,Access.randomAddress,List.append_assoc] using
          ((List.Sublist.refl [word w l.randomBase]).append hr₃).append hr₄
    · ram_cost
      simp only [work,childWork,he,if_neg (by omega : xs.length ≠ 0)]
      omega
    · ram_cost
      change 14+extraStack prepare ≤ 58 ∧ 6+extraStack round ≤ 58 ∧ f.frameSize+extraStack search ≤ 58 ∧
        18+extraStack children ≤ 58
      have h := rs.frame
      omega

/-- Additional live stack beyond the constructor frame; empty input bypasses
all grouping and search frames. -/
def peak (N : Nat) : Nat := if N = 0 then 17 else 58

/-- The complete source contract handles every random image and dirty memory.
Search outcomes are explicit, and all source effects obey the small workspace
policy needed by compiler simulation. -/
theorem contract {w free : Nat} (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (xs : List (Word w)) (l : Layout) (ha : Admissible w xs.length l)
    (f g : RamLang.Function) (root : Option (Word w)) (rootCost : Nat)
    (child : Word w → Fin (rootSlots xs) → Option (Word w)) (cost : Word w → Fin (rootSlots xs) → Nat)
    (rs : RootSpec p rho xs l f root rootCost)
    (cs : ∀ a, rootAccepted xs a = true → Children.SearchSpec p rho xs l a g (child a) (cost a))
    (hround : p.functions[1]? = some Hashing.Source.Rounding.function)
    (hfill : p.functions[2]? = some Fill.function)
    (hsample : p.functions[3]? = some Hashing.Source.Sampling.function)
    (hfind : p.functions[4]? = some Dedup.Source.Search.function)
    (hdedup : p.functions[5]? = some Dedup.Source.Pass.function)
    (hallocate : p.functions[8]? = some Allocation.function)
    (hchildren : p.functions[11]? = some Children.function)
    (hprepare : p.functions[13]? = some Prepare.function)
    (hempty : p.functions[14]? = some Empty.function)
    (hfree : peak xs.length ≤ free) (hinput : ArrayAt mem l.inputBase xs) :
    Contract p rho free Bounded.function.body
      ((arguments w xs.length l).map some ++ List.replicate Bounded.function.locals.length none) mem
      (fun flow mem' log => ∃ value, flow = .returned value ∧
        ((value = word w 0 ∧ Failed root child) ∨ Success xs l value mem') ∧
        (Source.policy w xs.length l).AllowsTrace log ∧
        (RamLang.Library.Retry.randomAddresses log).Sublist
          (consecutiveAddresses w l.randomBase (randomSpan w xs)))
      (work xs l ha rho root rootCost cost) (peak xs.length) := by
  by_cases hz : xs.length = 0
  · have hx : xs = [] := List.length_eq_zero_iff.mp hz
    subst xs
    apply (empty_contract p rho mem l ha hfill hempty (by simpa [peak] using hfree)).consequence
    · rintro flow mem' log ⟨value,hf,hs,hp,hr⟩
      exact ⟨value,hf,Or.inr hs,hp,by rw [hr]; exact List.nil_sublist _⟩
    · simp [work]
    · simp [peak]
  · simpa only [peak,if_neg hz] using nonempty_contract p rho mem xs l ha (by omega)
      f g root rootCost child cost rs cs hround hfill hsample hfind hdedup hallocate hchildren hprepare
      (by simpa [peak,hz] using hfree) hinput

/-- The highest simultaneous frame demand fits inside the existing scratch
suffix, including the smallest empty-input reservation. -/
theorem stack_sufficient (l : Layout) (N : Nat) : 30+peak N ≤ (Entry.stack l N).size := by
  simp only [peak,Entry.stack]
  split <;> omega

/-- Successful endpoint results cannot collide with the zero failure sentinel. -/
theorem Success.nonzero {w : Nat} {xs : List (Word w)} {l : Layout} {value : Word w} {mem : DataMemory w} (h : Success xs l value mem) : value ≠ word w 0 := by
  obtain ⟨r,_,rfl,hr,_⟩ := h
  have hf := Table.representation.fits hr
  have hn := Table.representation.nonempty hr
  intro he
  have hh := (word_eq_iff_of_lt hf (by unfold Region.Fits at hf; omega : 0 < modulus w)).mp he
  omega

end PerfectHash.Source.Constructor
