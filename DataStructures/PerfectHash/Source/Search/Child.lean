import DataStructures.PerfectHash.Source.Search.Root
import RamLang.Library.Search

namespace PerfectHash.Source.Search.Child
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Construction

set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- The child search is selected from the checked constructor source. -/
def function : RamLang.Function := Bounded.source.functions[10]'(by decide)

/-- The capped loop follows the empty and singleton fast paths. -/
def loop : Stmt := match function.body with | .seq _ (.seq _ (.seq s _)) => s | _ => .skip

/-- One charged sample, trial, and success test or counter advance. -/
def iteration : Stmt := match loop with | .while _ s => s | _ => .skip

/-- Parameters remain live across trials, with two arbitrary scratch locals. -/
def locals (nodes cursor table q : Nat) (shift : Word w) (c n : Nat)
    (seed accepted : Option (Word w)) : Locals w :=
  [some (word w nodes),some (word w cursor),some (word w table),some (word w q),some shift,
   some (word w c),some (word w n),none,seed,accepted]

/-- The child trial's application policy, extended by its reserved random block. -/
def policy (nodes N table q start total : Nat) : AccessPolicy w :=
  { Source.Child.policy nodes N table q with «random» := (Region.mk start total).Contains }

/-- The exact collision predicate computed by the child trial. -/
def accept (hash : Word w → Word w → Nat) (chain : List (Word w × Nat)) (seed : Word w) : Bool :=
  childAccepted (hash seed) [] (chain.map Prod.fst)

/-- A child attempt preserves its linked nodes on both outcomes, initializes
successful placement, and reads exactly one explicitly addressed random cell. -/
theorem iteration_contract {w free nodes N table q start total c n : Nat}
    (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (hash : Word w → Word w → Nat) (shift : Word w) (chain : List (Word w × Nat))
    (oldSeed oldAccepted : Option (Word w))
    (hsample : p.functions[3]? = some Hashing.Source.Sampling.function)
    (hchild : p.functions[7]? = some Source.Child.function)
    (hfill : p.functions[2]? = some RamLang.Logic.Fill.function) (hfree : 26 ≤ free)
    (hchain : Dedup.ChainAt mem nodes chain) (hb : ∀ item ∈ chain, 0 < item.2 ∧ item.2 ≤ N)
    (hh : ∀ seed key, hash seed key < q)
    (hhash : ∀ seed key, unsignedShiftRight (seed*key) shift = word w (hash seed key))
    (hnode : (Region.mk nodes (2*N)).Fits w) (htable : (Region.mk table (2*q)).Fits w)
    (hsep : (Region.mk nodes (2*N)).Separated ⟨table,2*q⟩)
    (hrandom : (Region.mk start total).Fits w) (hc : start ≤ c) (hn : c+n+1 ≤ start+total) :
    Contract p rho free iteration (locals nodes (Dedup.firstIndex chain) table q shift c (n+1) oldSeed oldAccepted) mem
      (fun flow mem' log => (policy nodes N table q start total).AllowsTrace log ∧
        RamLang.Library.Retry.randomAddresses log = [word w c] ∧ Dedup.ChainAt mem' nodes chain ∧
        if accept hash chain (Root.sample rho c) then
          flow = .returned (Root.sample rho c) ∧ SlotsAt (hash (Root.sample rho c)) q table (chain.map Prod.fst).reverse mem'
        else flow = .next (locals nodes (Dedup.firstIndex chain) table q shift (c+1) n
          (some (Root.sample rho c)) (some (word w 0))))
      (200*(q+chain.length+1)+150) 26 := by
  let sampled := Hashing.Source.Sampling.evaluation (free := free-7) p rho mem (word w c)
  have hsWork : instructions sampled = 32 := rfl
  have hsPeak : extraStack sampled = 0 := rfl
  have hr := Source.Child.contract (free := free-21) p rho mem (hash (Root.sample rho c)) (Root.sample rho c) shift chain
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
  have hpol : (policy nodes N table q start total).AllowsTrace
      ([.randomRead (word w c) (rho (word w c))]++log) := by
    apply (AccessPolicy.allowsTrace_append _).mpr
    constructor
    · intro e he
      simp only [List.mem_singleton] at he
      subst e
      change start ≤ (word w c).toNat ∧ (word w c).toNat < start+total
      have hr : start+total < modulus w := hrandom
      rw [word_toNat_of_lt (by omega : c < modulus w)]
      omega
    · intro e he
      have hh := hpolicy e he
      cases e <;> first | exact hh | exact False.elim hh
  have hrandomLog : RamLang.Library.Retry.randomAddresses
      ([.randomRead (word w c) (rho (word w c))]++log) = [word w c] := by
    rw [RamLang.Library.Retry.randomAddresses_append,hrandomNone]
    rfl
  have hone : 1 < modulus w := by have hf : nodes+2*N < modulus w := hnode; have hr : start+total < modulus w := hrandom; omega
  have hnfit : n+1 < modulus w := by have hr : start+total < modulus w := hrandom; omega
  have hminus : word w (n+1)-word w 1 = word w n := by
    rw [WordRam.word_sub (n+1) 1 hone (by omega)]
    simp
  have hsampleSpace : 7 ≤ free := by omega
  have hchildSpace : 21 ≤ free := by omega
  cases hy : accept hash chain (Root.sample rho c) with
  | false =>
    change flow = .returned (word w (if accept hash chain (Root.sample rho c) then 1 else 0)) at hflow
    simp only [hy,Bool.false_eq_true,↓reduceIte] at hflow
    subst flow
    refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · simp only [hy,Bool.false_eq_true,↓reduceIte,Option.toList_none,List.nil_append,List.append_nil]
      refine ⟨hpol,hrandomLog,harray,?_⟩
      simp [locals,Binary.eval,Root.sample,WordRam.word_add,hminus]
    · ram_cost
      omega
    · ram_cost
      change 7+extraStack sampled ≤ 26 ∧ 21+extraStack child ≤ 26
      omega
  | true =>
    change flow = .returned (word w (if accept hash chain (Root.sample rho c) then 1 else 0)) at hflow
    simp only [hy,↓reduceIte] at hflow
    subst flow
    have hnonzero : word w 1 ≠ word w 0 := by
      intro he
      have hh := (word_eq_iff_of_lt hone (by omega : 0 < modulus w)).mp he
      omega
    refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · simpa [hy,Root.sample] using And.intro hpol (And.intro hrandomLog (And.intro harray (hslots hy)))
    · ram_cost
      omega
    · ram_cost
      change 7+extraStack sampled ≤ 26 ∧ 21+extraStack child ≤ 26
      omega

/-- Complete bounded search for a child with at least two slots, with exact selected seed and addressed prefix.
The instruction allowance depends on attempts actually made, not on the cap. -/
theorem contract {w free nodes N table q start total : Nat}
    (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (hash : Word w → Word w → Nat) (shift : Word w) (chain : List (Word w × Nat))
    (hsample : p.functions[3]? = some Hashing.Source.Sampling.function)
    (hchild : p.functions[7]? = some Source.Child.function)
    (hfill : p.functions[2]? = some RamLang.Logic.Fill.function) (hfree : 26 ≤ free)
    (hchain : Dedup.ChainAt mem nodes chain) (hb : ∀ item ∈ chain, 0 < item.2 ∧ item.2 ≤ N)
    (hh : ∀ seed key, hash seed key < q)
    (hhash : ∀ seed key, unsignedShiftRight (seed*key) shift = word w (hash seed key))
    (hnode : (Region.mk nodes (2*N)).Fits w) (htable : (Region.mk table (2*q)).Fits w)
    (hsep : (Region.mk nodes (2*N)).Separated ⟨table,2*q⟩)
    (hq : 1 < q)
    (hrandom : (Region.mk start total).Fits w) :
    Contract p rho free function.body
      ([word w nodes,word w (Dedup.firstIndex chain),word w table,word w q,shift,word w start,word w total].map some ++
        List.replicate function.locals.length none) mem
      (fun flow mem' log =>
        flow = .returned ((RamLang.Library.Search.choice (Root.sample rho) (accept hash chain) start total).getD (word w 0)) ∧
        (∀ seed, RamLang.Library.Search.choice (Root.sample rho) (accept hash chain) start total = some seed →
          SlotsAt (hash seed) q table (chain.map Prod.fst).reverse mem') ∧ Dedup.ChainAt mem' nodes chain ∧
        (policy nodes N table q start total).AllowsTrace log ∧
        RamLang.Library.Retry.randomAddresses log = RamLang.Library.Retry.addresses w start
          (RamLang.Library.Search.attempts (Root.sample rho) (accept hash chain) start total))
      ((200*(q+chain.length+1)+155)*RamLang.Library.Search.attempts (Root.sample rho) (accept hash chain) start total+30) 26 := by
  have hqfit : q < modulus w := by have hf : table+2*q < modulus w := htable; omega
  have hone : 1 < modulus w := by omega
  have hzero : word w q ≠ word w 0 := by
    intro he
    have := (word_eq_iff_of_lt hqfit (by omega : 0 < modulus w)).mp he
    omega
  have hqMod : q % modulus w = q := Nat.mod_eq_of_lt hqfit
  have hOneMod : 1 % modulus w = 1 := Nat.mod_eq_of_lt hone
  let I (c n : Nat) (ls : Locals w) (memory : DataMemory w) : Prop :=
    start ≤ c ∧ c+n ≤ start+total ∧ Dedup.ChainAt memory nodes chain ∧
      ∃ oldSeed oldAccepted, ls = locals nodes (Dedup.firstIndex chain) table q shift c n oldSeed oldAccepted
  have counterValue : ∀ c n ls memory, I c n ls memory →
      (.local 6 : Atom).eval ls = .ok (word w n) ∧ n < modulus w := by
    rintro c n ls memory ⟨hc,hn,ha,seed,accepted,rfl⟩
    refine ⟨rfl,?_⟩
    have hr : start+total < modulus w := hrandom
    omega
  have trial : ∀ c n ls memory, I c (n+1) ls memory →
      Contract p rho free iteration ls memory
        (fun flow mem' log => (policy nodes N table q start total).AllowsTrace log ∧
          RamLang.Library.Retry.randomAddresses log = [word w c] ∧
          if accept hash chain (Root.sample rho c) then
            flow = .returned (Root.sample rho c) ∧ SlotsAt (hash (Root.sample rho c)) q table (chain.map Prod.fst).reverse mem' ∧ Dedup.ChainAt mem' nodes chain
          else ∃ out, flow = .next out ∧ I (c+1) n out mem') (200*(q+chain.length+1)+150) 26 := by
    rintro c n ls memory ⟨hc,hn,ha,seed,accepted,rfl⟩
    apply (iteration_contract p rho memory hash shift chain seed accepted hsample hchild hfill hfree
      ha hb hh hhash hnode htable hsep hrandom hc (by omega)).consequence (work' := 200*(q+chain.length+1)+150) (peak' := 26)
    · rintro flow mem' log ⟨hp,hr,ha',hq⟩
      refine ⟨hp,hr,?_⟩
      cases hy : accept hash chain (Root.sample rho c) with
      | true => simpa [hy,and_assoc] using And.intro hq ha'
      | false =>
        simp only [hy,Bool.false_eq_true,↓reduceIte] at hq ⊢
        exact ⟨_,hq,by dsimp [I]; exact ⟨by omega,by omega,ha',_,_,rfl⟩⟩
    · exact Nat.le_refl _
    · exact Nat.le_refl _
  have hi : I start total (locals nodes (Dedup.firstIndex chain) table q shift start total none none) mem :=
    ⟨Nat.le_refl _,Nat.le_refl _,hchain,none,none,rfl⟩
  obtain ⟨flow,mem',log,d,⟨hq,hp,hr⟩,ht,hs⟩ :=
    RamLang.Library.Search.loop_contract 6 iteration (Root.sample rho) (accept hash chain) I
      (fun seed memory => SlotsAt (hash seed) q table (chain.map Prod.fst).reverse memory ∧ Dedup.ChainAt memory nodes chain)
      (policy nodes N table q start total) (200*(q+chain.length+1)+150) 26
      counterValue trial start total _ mem hi
  cases he : RamLang.Library.Search.choice (Root.sample rho) (accept hash chain) start total with
  | none =>
    simp only [RamLang.Library.Search.Post,he] at hq
    obtain ⟨out,rfl,_,_,ha,seed,accepted,hout⟩ := hq
    subst out
    refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · simpa [he] using And.intro ha (And.intro hp hr)
    · ram_cost
      simp only [Nat.add_assoc, Nat.reduceAdd] at ht ⊢
      omega
    · ram_cost
      exact hs
  | some seed =>
    simp only [RamLang.Library.Search.Post,he] at hq
    obtain ⟨rfl,hgroup,ha⟩ := hq
    refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · simpa [he] using And.intro hgroup (And.intro ha (And.intro hp hr))
    · ram_cost
      simp only [Nat.add_assoc, Nat.reduceAdd] at ht ⊢
      omega
    · ram_cost
      exact hs

/-- Empty children return the conventional seed one without touching ordinary
or random memory. There are no zero-length hash-range assumptions. -/
theorem empty_contract {w free : Nat} (p : RamLang.Program) (rho : RandomMemory w)
    (mem : DataMemory w) (nodes cursor table shift address tries : Word w) :
    Contract p rho free function.body
      ([nodes,cursor,table,word w 0,shift,address,tries].map some ++ List.replicate function.locals.length none) mem
      (fun flow mem' log => flow = .returned (word w 1) ∧ mem' = mem ∧ log = []) 11 0 := by
  refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
  · exact ⟨rfl,rfl,rfl⟩
  · ram_cost
  · ram_cost

/-- A singleton's direct seed is executed by the ordinary child helper. Its
slot invariant is the same one used by hashed children, with no random read. -/
theorem singleton_contract {w free nodes N table : Nat}
    (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (hash : Word w → Nat) (shift address tries : Word w) (chain : List (Word w × Nat))
    (hchild : p.functions[7]? = some Source.Child.function)
    (hfill : p.functions[2]? = some RamLang.Logic.Fill.function) (hfree : 26 ≤ free)
    (hchain : Dedup.ChainAt mem nodes chain) (hb : ∀ item ∈ chain, 0 < item.2 ∧ item.2 ≤ N)
    (hh : ∀ key, hash key < 1)
    (hhash : ∀ key, unsignedShiftRight (word w 1*key) shift = word w (hash key))
    (hnode : (Region.mk nodes (2*N)).Fits w) (htable : (Region.mk table 2).Fits w)
    (hsep : (Region.mk nodes (2*N)).Separated ⟨table,2⟩)
    (haccept : childAccepted hash [] (chain.map Prod.fst) = true) :
    Contract p rho free function.body
      ([word w nodes,word w (Dedup.firstIndex chain),word w table,word w 1,shift,address,tries].map some ++
        List.replicate function.locals.length none) mem
      (fun flow mem' log => flow = .returned (word w 1) ∧
        SlotsAt hash 1 table (chain.map Prod.fst).reverse mem' ∧ Dedup.ChainAt mem' nodes chain ∧
        (Source.Child.policy nodes N table 1).AllowsTrace log ∧ RamLang.Library.Retry.randomAddresses log = [])
      (200*(chain.length+2)+60) 26 := by
  obtain ⟨flow,mem',log,child,⟨hf,hs,hp⟩,ht,hpeak⟩ := Source.Child.contract (free := free-21)
    p rho mem hash (word w 1) shift chain hfill (by omega) hchain hb hh hhash hnode htable hsep
  simp only [haccept,↓reduceIte] at hf
  subst flow
  have hslots := hs haccept
  have hchain' := hchain.frame hb hnode (fun a ha =>
    (child.frame_of_policy hp (Region.not_contains_of_separated hsep ha)).symm)
  have hr : RamLang.Library.Retry.randomAddresses log = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro e he
    have hh := hp e he
    cases e <;> simp_all [Source.Child.policy,AccessPolicy.Allows,Access.randomAddress]
  have hone : 1 < modulus w := by have ht : table+2 < modulus w := htable; omega
  have hne : word w 1 ≠ word w 0 := by
    intro he
    have := (word_eq_iff_of_lt hone (by omega : 0 < modulus w)).mp he
    omega
  have hchildSpace : 21 ≤ free := by omega
  refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
  · simpa using And.intro hslots (And.intro hchain' (And.intro hp hr))
  · ram_cost
    omega
  · ram_cost
    change 21+extraStack child ≤ 26
    omega

end PerfectHash.Source.Search.Child
