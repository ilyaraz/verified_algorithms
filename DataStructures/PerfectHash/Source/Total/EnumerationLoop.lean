import DataStructures.PerfectHash.Source.Total.EnumerationTrial

namespace PerfectHash.Source.Search.Root
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Construction
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- A successful ghost prefix proves termination of the ordinary infinite-form source loop. -/
theorem enumeration_contract {w free input dir nodes m start total c n H : Nat}
    (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (hash : Word w → Word w → Fin m) (shift : Word w) (keys : List (Word w))
    (oldAccepted : Option (Word w)) (value : Word w)
    (hroot : p.functions[6]? = some Source.Root.function)
    (hfill : p.functions[2]? = some RamLang.Logic.Fill.function) (hfree : 34 ≤ free)
    (hspace : GroupSpace w m keys.length dir nodes) (hlinear : 64*(keys.length+1) < modulus w)
    (hinput : ArrayAt mem input keys)
    (hhash : ∀ seed key, unsignedShiftRight (seed*key) shift = word w (hash seed key).val)
    (hfit : (Region.mk input keys.length).Fits w)
    (hdir : (Region.mk input keys.length).Separated ⟨dir,4*m⟩)
    (hnodes : (Region.mk input keys.length).Separated ⟨nodes,2*keys.length⟩)
    (hone : 1 < modulus w)
    (hf : RamLang.Library.Search.choice (PerfectHash.Total.candidate w) (accept hash keys) 0 H = some value) :
    Contract p rho free Total.rootLoop (locals input keys.length dir nodes m shift c n (some (word w 1)) oldAccepted) mem
      (fun flow memory log => flow = .returned value ∧
        (Grouped (hash value) dir nodes keys.reverse memory ∧ ArrayAt memory input keys) ∧
        (policy input keys.length dir nodes m start total).AllowsTrace log ∧ RamLang.Library.Retry.randomAddresses log = [])
      ((300*(keys.length+m+1)+150+4)*H) 34 := by
  let I (i : Nat) (ls : Locals w) (memory : DataMemory w) : Prop :=
    ArrayAt memory input keys ∧ ∃ accepted, ls = locals input keys.length dir nodes m shift c n (some (PerfectHash.Total.candidate w i)) accepted
  have trial : ∀ i ls memory, I i ls memory →
      Contract p rho free Total.rootIteration ls memory
        (fun flow mem' log => (policy input keys.length dir nodes m start total).AllowsTrace log ∧
          RamLang.Library.Retry.randomAddresses log = [] ∧
          if accept hash keys (PerfectHash.Total.candidate w i) then
            flow = .returned (PerfectHash.Total.candidate w i) ∧
              (Grouped (hash (PerfectHash.Total.candidate w i)) dir nodes keys.reverse mem' ∧ ArrayAt mem' input keys)
          else ∃ out, flow = .next out ∧ I (i+1) out mem') (300*(keys.length+m+1)+150) 34 := by
    rintro i ls memory ⟨ha,accepted,rfl⟩
    apply (enumeration_iteration (start := start) (total := total) p rho memory hash shift keys accepted hroot hfill hfree hspace hlinear ha hhash hfit hdir hnodes hone).consequence
    · rintro flow mem' log ⟨hp,hr,ha',hq⟩
      refine ⟨hp,hr,?_⟩
      cases hy : accept hash keys (PerfectHash.Total.candidate w i) with
      | true => simpa [hy,and_assoc] using And.intro hq ha'
      | false =>
        simp only [hy,Bool.false_eq_true,↓reduceIte] at hq ⊢
        exact ⟨_,hq,ha',_,rfl⟩
    · exact Nat.le_refl _
    · exact Nat.le_refl _
  exact RamLang.Library.Enumeration.loop_contract _ _ _ I
    (fun seed memory => Grouped (hash seed) dir nodes keys.reverse memory ∧ ArrayAt memory input keys)
    (policy input keys.length dir nodes m start total) (300*(keys.length+m+1)+150) 34 hone trial 0 H _ mem value ⟨hinput,oldAccepted,rfl⟩ hf

end PerfectHash.Source.Search.Root

namespace PerfectHash.Source.Search.Child
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Construction
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- A successful ghost prefix proves termination of the ordinary infinite-form source loop. -/
theorem enumeration_contract {w free nodes N table q start total c n H : Nat}
    (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (hash : Word w → Word w → Nat) (shift : Word w) (chain : List (Word w × Nat))
    (oldAccepted : Option (Word w)) (value : Word w)
    (hchild : p.functions[7]? = some Source.Child.function)
    (hfill : p.functions[2]? = some RamLang.Logic.Fill.function) (hfree : 26 ≤ free)
    (hchain : Dedup.ChainAt mem nodes chain) (hb : ∀ item ∈ chain, 0 < item.2 ∧ item.2 ≤ N)
    (hh : ∀ seed key, hash seed key < q)
    (hhash : ∀ seed key, unsignedShiftRight (seed*key) shift = word w (hash seed key))
    (hnode : (Region.mk nodes (2*N)).Fits w) (htable : (Region.mk table (2*q)).Fits w)
    (hsep : (Region.mk nodes (2*N)).Separated ⟨table,2*q⟩)
    (hone : 1 < modulus w)
    (hf : RamLang.Library.Search.choice (PerfectHash.Total.candidate w) (accept hash chain) 0 H = some value) :
    Contract p rho free Total.childLoop (locals nodes (Dedup.firstIndex chain) table q shift c n (some (word w 1)) oldAccepted) mem
      (fun flow memory log => flow = .returned value ∧
        (SlotsAt (hash value) q table (chain.map Prod.fst).reverse memory ∧ Dedup.ChainAt memory nodes chain) ∧
        (policy nodes N table q start total).AllowsTrace log ∧ RamLang.Library.Retry.randomAddresses log = [])
      ((200*(q+chain.length+1)+150+4)*H) 26 := by
  let I (i : Nat) (ls : Locals w) (memory : DataMemory w) : Prop :=
    Dedup.ChainAt memory nodes chain ∧ ∃ accepted, ls = locals nodes (Dedup.firstIndex chain) table q shift c n (some (PerfectHash.Total.candidate w i)) accepted
  have trial : ∀ i ls memory, I i ls memory →
      Contract p rho free Total.childIteration ls memory
        (fun flow mem' log => (policy nodes N table q start total).AllowsTrace log ∧
          RamLang.Library.Retry.randomAddresses log = [] ∧
          if accept hash chain (PerfectHash.Total.candidate w i) then
            flow = .returned (PerfectHash.Total.candidate w i) ∧
              (SlotsAt (hash (PerfectHash.Total.candidate w i)) q table (chain.map Prod.fst).reverse mem' ∧ Dedup.ChainAt mem' nodes chain)
          else ∃ out, flow = .next out ∧ I (i+1) out mem') (200*(q+chain.length+1)+150) 26 := by
    rintro i ls memory ⟨ha,accepted,rfl⟩
    apply (enumeration_iteration (start := start) (total := total) p rho memory hash shift chain accepted hchild hfill hfree ha hb hh hhash hnode htable hsep hone).consequence
    · rintro flow mem' log ⟨hp,hr,ha',hq⟩
      refine ⟨hp,hr,?_⟩
      cases hy : accept hash chain (PerfectHash.Total.candidate w i) with
      | true => simpa [hy,and_assoc] using And.intro hq ha'
      | false =>
        simp only [hy,Bool.false_eq_true,↓reduceIte] at hq ⊢
        exact ⟨_,hq,ha',_,rfl⟩
    · exact Nat.le_refl _
    · exact Nat.le_refl _
  exact RamLang.Library.Enumeration.loop_contract _ _ _ I
    (fun seed memory => SlotsAt (hash seed) q table (chain.map Prod.fst).reverse memory ∧ Dedup.ChainAt memory nodes chain)
    (policy nodes N table q start total) (200*(q+chain.length+1)+150) 26 hone trial 0 H _ mem value ⟨hchain,oldAccepted,rfl⟩ hf

end PerfectHash.Source.Search.Child
