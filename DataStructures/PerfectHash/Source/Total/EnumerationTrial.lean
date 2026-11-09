import DataStructures.PerfectHash.Source.Total.Program
import DataStructures.PerfectHash.Source.Total.RandomPrefix
import DataStructures.PerfectHash.Total.Selection
import RamLang.Library.Enumeration

namespace PerfectHash.Source.Search.Root
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Construction
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- One deterministic candidate is tested without a random read; rejection advances the odd seed. -/
theorem enumeration_iteration {w free input dir nodes m start total c n i : Nat}
    (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (hash : Word w → Word w → Fin m) (shift : Word w) (keys : List (Word w))
    (oldAccepted : Option (Word w))
    (hroot : p.functions[6]? = some Source.Root.function)
    (hfill : p.functions[2]? = some RamLang.Logic.Fill.function) (hfree : 34 ≤ free)
    (hspace : GroupSpace w m keys.length dir nodes) (hlinear : 64*(keys.length+1) < modulus w)
    (hinput : ArrayAt mem input keys)
    (hhash : ∀ seed key, unsignedShiftRight (seed*key) shift = word w (hash seed key).val)
    (hfit : (Region.mk input keys.length).Fits w)
    (hdir : (Region.mk input keys.length).Separated ⟨dir,4*m⟩)
    (hnodes : (Region.mk input keys.length).Separated ⟨nodes,2*keys.length⟩)
    (hone : 1 < modulus w) :
    Contract p rho free Total.rootIteration (locals input keys.length dir nodes m shift c n (some (PerfectHash.Total.candidate w i)) oldAccepted) mem
      (fun flow mem' log => (policy input keys.length dir nodes m start total).AllowsTrace log ∧
        RamLang.Library.Retry.randomAddresses log = [] ∧ ArrayAt mem' input keys ∧
        if accept hash keys (PerfectHash.Total.candidate w i) then
          flow = .returned (PerfectHash.Total.candidate w i) ∧ Grouped (hash (PerfectHash.Total.candidate w i)) dir nodes keys.reverse mem'
        else flow = .next (locals input keys.length dir nodes m shift c n
          (some (PerfectHash.Total.candidate w (i+1))) (some (word w 0))))
      (300*(keys.length+m+1)+150) 34 := by
  have hr := Source.Root.contract (free := free-29) p rho mem (hash (PerfectHash.Total.candidate w i)) (PerfectHash.Total.candidate w i) shift keys
    hfill (by omega) hspace rfl hlinear hinput (hhash _) hfit hdir hnodes
  obtain ⟨flow,mem',log,root,⟨hflow,hgroup,hpolicy⟩,hwork,hpeak⟩ := hr
  have hrandomNone : RamLang.Library.Retry.randomAddresses log = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro e he
    have hh := hpolicy e he
    cases e <;> simp_all [Source.Root.policy,AccessPolicy.Allows,Access.randomAddress]
  have harray : ArrayAt mem' input keys := by
    apply hinput.congr hfit
    intro a ha
    symm
    apply root.frame_of_policy hpolicy
    exact not_or.mpr ⟨Region.not_contains_of_separated hdir ha,Region.not_contains_of_separated hnodes ha⟩
  have hpol : (policy input keys.length dir nodes m start total).AllowsTrace log := by
    intro e he
    have hh := hpolicy e he
    cases e <;> first | exact hh | exact False.elim hh
  have hrootSpace : 29 ≤ free := by omega
  cases hy : accept hash keys (PerfectHash.Total.candidate w i) with
  | false =>
    change flow = .returned (word w (if accept hash keys (PerfectHash.Total.candidate w i) then 1 else 0)) at hflow
    simp only [hy,Bool.false_eq_true,↓reduceIte] at hflow
    subst flow
    refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · simp only [hy,Bool.false_eq_true,↓reduceIte,Option.toList_none,List.nil_append,List.append_nil]
      refine ⟨hpol,hrandomNone,harray,?_⟩
      simp [locals,Binary.eval,PerfectHash.Total.candidate_next]
    · ram_cost
      omega
    · ram_cost
      change 29+extraStack root ≤ 34
      omega
  | true =>
    change flow = .returned (word w (if accept hash keys (PerfectHash.Total.candidate w i) then 1 else 0)) at hflow
    simp only [hy,↓reduceIte] at hflow
    subst flow
    have hnonzero : word w 1 ≠ word w 0 := by
      intro he
      have hh := (word_eq_iff_of_lt hone (by omega : 0 < modulus w)).mp he
      omega
    refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · simpa [hy] using And.intro hpol (And.intro hrandomNone (And.intro harray (hgroup hy)))
    · ram_cost
      omega
    · ram_cost
      change 29+extraStack root ≤ 34
      omega


end PerfectHash.Source.Search.Root

namespace PerfectHash.Source.Search.Child
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Construction
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- One deterministic candidate is tested without a random read; rejection advances the odd seed. -/
theorem enumeration_iteration {w free nodes N table q start total c n i : Nat}
    (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (hash : Word w → Word w → Nat) (shift : Word w) (chain : List (Word w × Nat))
    (oldAccepted : Option (Word w))
    (hchild : p.functions[7]? = some Source.Child.function)
    (hfill : p.functions[2]? = some RamLang.Logic.Fill.function) (hfree : 26 ≤ free)
    (hchain : Dedup.ChainAt mem nodes chain) (hb : ∀ item ∈ chain, 0 < item.2 ∧ item.2 ≤ N)
    (hh : ∀ seed key, hash seed key < q)
    (hhash : ∀ seed key, unsignedShiftRight (seed*key) shift = word w (hash seed key))
    (hnode : (Region.mk nodes (2*N)).Fits w) (htable : (Region.mk table (2*q)).Fits w)
    (hsep : (Region.mk nodes (2*N)).Separated ⟨table,2*q⟩)
    (hone : 1 < modulus w) :
    Contract p rho free Total.childIteration (locals nodes (Dedup.firstIndex chain) table q shift c n (some (PerfectHash.Total.candidate w i)) oldAccepted) mem
      (fun flow mem' log => (policy nodes N table q start total).AllowsTrace log ∧
        RamLang.Library.Retry.randomAddresses log = [] ∧ Dedup.ChainAt mem' nodes chain ∧
        if accept hash chain (PerfectHash.Total.candidate w i) then
          flow = .returned (PerfectHash.Total.candidate w i) ∧ SlotsAt (hash (PerfectHash.Total.candidate w i)) q table (chain.map Prod.fst).reverse mem'
        else flow = .next (locals nodes (Dedup.firstIndex chain) table q shift c n
          (some (PerfectHash.Total.candidate w (i+1))) (some (word w 0))))
      (200*(q+chain.length+1)+150) 26 := by
  have hr := Source.Child.contract (free := free-21) p rho mem (hash (PerfectHash.Total.candidate w i)) (PerfectHash.Total.candidate w i) shift chain
    hfill (by omega) hchain hb (hh _) (hhash _) hnode htable hsep
  obtain ⟨flow,mem',log,child,⟨hflow,hslots,hpolicy⟩,hwork,hpeak⟩ := hr
  have hrandomNone : RamLang.Library.Retry.randomAddresses log = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro e he
    have hh := hpolicy e he
    cases e <;> simp_all [Source.Child.policy,AccessPolicy.Allows,Access.randomAddress]
  have harray : Dedup.ChainAt mem' nodes chain :=
    hchain.frame hb hnode (fun a ha =>
      (child.frame_of_policy hpolicy (Region.not_contains_of_separated hsep ha)).symm)
  have hpol : (policy nodes N table q start total).AllowsTrace log := by
    intro e he
    have hh := hpolicy e he
    cases e <;> first | exact hh | exact False.elim hh
  have hchildSpace : 21 ≤ free := by omega
  cases hy : accept hash chain (PerfectHash.Total.candidate w i) with
  | false =>
    change flow = .returned (word w (if accept hash chain (PerfectHash.Total.candidate w i) then 1 else 0)) at hflow
    simp only [hy,Bool.false_eq_true,↓reduceIte] at hflow
    subst flow
    refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · simp only [hy,Bool.false_eq_true,↓reduceIte,Option.toList_none,List.nil_append,List.append_nil]
      refine ⟨hpol,hrandomNone,harray,?_⟩
      simp [locals,Binary.eval,PerfectHash.Total.candidate_next]
    · ram_cost
      omega
    · ram_cost
      change 21+extraStack child ≤ 26
      omega
  | true =>
    change flow = .returned (word w (if accept hash chain (PerfectHash.Total.candidate w i) then 1 else 0)) at hflow
    simp only [hy,↓reduceIte] at hflow
    subst flow
    have hnonzero : word w 1 ≠ word w 0 := by
      intro he
      have hh := (word_eq_iff_of_lt hone (by omega : 0 < modulus w)).mp he
      omega
    refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · simpa [hy] using And.intro hpol (And.intro hrandomNone (And.intro harray (hslots hy)))
    · ram_cost
      omega
    · ram_cost
      change 21+extraStack child ≤ 26
      omega


end PerfectHash.Source.Search.Child
