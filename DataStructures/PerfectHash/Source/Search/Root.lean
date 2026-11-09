import DataStructures.PerfectHash.Source.Bounded.Program
import RamLang.Library.Search

namespace PerfectHash.Source.Search.Root
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Construction

set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- The root search is selected from the checked constructor source. -/
def function : RamLang.Function := Bounded.source.functions[9]'(by decide)

/-- The first statement is the capped retry loop. -/
def loop : Stmt := match function.body with | .seq s _ => s | _ => .skip

/-- One charged sample, trial, and success test or counter advance. -/
def iteration : Stmt := match loop with | .while _ s => s | _ => .skip

/-- Parameters remain live across trials, with two arbitrary scratch locals. -/
def locals (input N dir nodes m : Nat) (shift : Word w) (c n : Nat)
    (seed accepted : Option (Word w)) : Locals w :=
  [some (word w input),some (word w N),some (word w dir),some (word w nodes),some (word w m),some shift,
   some (word w c),some (word w n),seed,accepted]

/-- The root trial's application policy, extended by its reserved random block. -/
def policy (input N dir nodes m start total : Nat) : AccessPolicy w :=
  { Source.Root.policy ⟨input,N⟩ dir nodes m N with «random» := (Region.mk start total).Contains }

/-- The seed computed at one addressed random-memory cell. -/
def sample (rho : RandomMemory w) (c : Nat) : Word w := Hashing.MultiplyShift.sample (rho (word w c))

/-- The exact root acceptance condition implemented by the verified trial. -/
def accept (hash : Word w → Word w → Fin m) (keys : List (Word w)) (seed : Word w) : Bool :=
  groupAccepted (hash seed) (6*keys.length) [] keys

macro "search_test" : tactic => `(tactic|
  simp [Condition.eval,Atom.eval,requireSome,Comparison.test,Binary.eval,
    bind,pure,Except.bind,Except.pure,WordRam.word_add,WordRam.word_mul, *])

/-- A root attempt preserves its compact input on both outcomes, initializes
successful grouping, and reads exactly one explicitly addressed random cell. -/
theorem iteration_contract {w free input dir nodes m start total c n : Nat}
    (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (hash : Word w → Word w → Fin m) (shift : Word w) (keys : List (Word w))
    (oldSeed oldAccepted : Option (Word w))
    (hsample : p.functions[3]? = some Hashing.Source.Sampling.function)
    (hroot : p.functions[6]? = some Source.Root.function)
    (hfill : p.functions[2]? = some RamLang.Logic.Fill.function) (hfree : 34 ≤ free)
    (hspace : GroupSpace w m keys.length dir nodes) (hlinear : 64*(keys.length+1) < modulus w)
    (hinput : ArrayAt mem input keys)
    (hhash : ∀ seed key, unsignedShiftRight (seed*key) shift = word w (hash seed key).val)
    (hfit : (Region.mk input keys.length).Fits w)
    (hdir : (Region.mk input keys.length).Separated ⟨dir,4*m⟩)
    (hnodes : (Region.mk input keys.length).Separated ⟨nodes,2*keys.length⟩)
    (hrandom : (Region.mk start total).Fits w) (hc : start ≤ c) (hn : c+n+1 ≤ start+total) :
    Contract p rho free iteration (locals input keys.length dir nodes m shift c (n+1) oldSeed oldAccepted) mem
      (fun flow mem' log => (policy input keys.length dir nodes m start total).AllowsTrace log ∧
        RamLang.Library.Retry.randomAddresses log = [word w c] ∧ ArrayAt mem' input keys ∧
        if accept hash keys (sample rho c) then
          flow = .returned (sample rho c) ∧ Grouped (hash (sample rho c)) dir nodes keys.reverse mem'
        else flow = .next (locals input keys.length dir nodes m shift (c+1) n
          (some (sample rho c)) (some (word w 0))))
      (300*(keys.length+m+1)+150) 34 := by
  let sampled := Hashing.Source.Sampling.evaluation (free := free-7) p rho mem (word w c)
  have hsWork : instructions sampled = 32 := rfl
  have hsPeak : extraStack sampled = 0 := rfl
  have hr := Source.Root.contract (free := free-29) p rho mem (hash (sample rho c)) (sample rho c) shift keys
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
  have hpol : (policy input keys.length dir nodes m start total).AllowsTrace
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
  have hone : 1 < modulus w := by omega
  have hnfit : n+1 < modulus w := by have hr : start+total < modulus w := hrandom; omega
  have hminus : word w (n+1)-word w 1 = word w n := by
    rw [WordRam.word_sub (n+1) 1 hone (by omega)]
    simp
  have hsampleSpace : 7 ≤ free := by omega
  have hrootSpace : 29 ≤ free := by omega
  cases hy : accept hash keys (sample rho c) with
  | false =>
    change flow = .returned (word w (if accept hash keys (sample rho c) then 1 else 0)) at hflow
    simp only [hy,Bool.false_eq_true,↓reduceIte] at hflow
    subst flow
    refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · simp only [hy,Bool.false_eq_true,↓reduceIte,Option.toList_none,List.nil_append,List.append_nil]
      refine ⟨hpol,hrandomLog,harray,?_⟩
      simp [locals,Binary.eval,sample,WordRam.word_add,hminus]
    · ram_cost
      omega
    · ram_cost
      change 7+extraStack sampled ≤ 34 ∧ 29+extraStack root ≤ 34
      omega
  | true =>
    change flow = .returned (word w (if accept hash keys (sample rho c) then 1 else 0)) at hflow
    simp only [hy,↓reduceIte] at hflow
    subst flow
    have hnonzero : word w 1 ≠ word w 0 := by
      intro he
      have hh := (word_eq_iff_of_lt hone (by omega : 0 < modulus w)).mp he
      omega
    refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · simpa [hy,sample] using And.intro hpol (And.intro hrandomLog (And.intro harray (hgroup hy)))
    · ram_cost
      omega
    · ram_cost
      change 7+extraStack sampled ≤ 34 ∧ 29+extraStack root ≤ 34
      omega

/-- Complete bounded root search, with exact selected seed and addressed prefix.
The instruction allowance depends on attempts actually made, not on the cap. -/
theorem contract {w free input dir nodes m start total : Nat}
    (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (hash : Word w → Word w → Fin m) (shift : Word w) (keys : List (Word w))
    (hsample : p.functions[3]? = some Hashing.Source.Sampling.function)
    (hroot : p.functions[6]? = some Source.Root.function)
    (hfill : p.functions[2]? = some RamLang.Logic.Fill.function) (hfree : 34 ≤ free)
    (hspace : GroupSpace w m keys.length dir nodes) (hlinear : 64*(keys.length+1) < modulus w)
    (hinput : ArrayAt mem input keys)
    (hhash : ∀ seed key, unsignedShiftRight (seed*key) shift = word w (hash seed key).val)
    (hfit : (Region.mk input keys.length).Fits w)
    (hdir : (Region.mk input keys.length).Separated ⟨dir,4*m⟩)
    (hnodes : (Region.mk input keys.length).Separated ⟨nodes,2*keys.length⟩)
    (hrandom : (Region.mk start total).Fits w) :
    Contract p rho free function.body
      ([word w input,word w keys.length,word w dir,word w nodes,word w m,shift,word w start,word w total].map some ++
        List.replicate function.locals.length none) mem
      (fun flow mem' log =>
        flow = .returned ((RamLang.Library.Search.choice (sample rho) (accept hash keys) start total).getD (word w 0)) ∧
        (∀ seed, RamLang.Library.Search.choice (sample rho) (accept hash keys) start total = some seed →
          Grouped (hash seed) dir nodes keys.reverse mem') ∧ ArrayAt mem' input keys ∧
        (policy input keys.length dir nodes m start total).AllowsTrace log ∧
        RamLang.Library.Retry.randomAddresses log = RamLang.Library.Retry.addresses w start
          (RamLang.Library.Search.attempts (sample rho) (accept hash keys) start total))
      ((300*(keys.length+m+1)+155)*RamLang.Library.Search.attempts (sample rho) (accept hash keys) start total+12) 34 := by
  let I (c n : Nat) (ls : Locals w) (memory : DataMemory w) : Prop :=
    start ≤ c ∧ c+n ≤ start+total ∧ ArrayAt memory input keys ∧
      ∃ oldSeed oldAccepted, ls = locals input keys.length dir nodes m shift c n oldSeed oldAccepted
  have counterValue : ∀ c n ls memory, I c n ls memory →
      (.local 7 : Atom).eval ls = .ok (word w n) ∧ n < modulus w := by
    rintro c n ls memory ⟨hc,hn,ha,seed,accepted,rfl⟩
    refine ⟨rfl,?_⟩
    have hr : start+total < modulus w := hrandom
    omega
  have trial : ∀ c n ls memory, I c (n+1) ls memory →
      Contract p rho free iteration ls memory
        (fun flow mem' log => (policy input keys.length dir nodes m start total).AllowsTrace log ∧
          RamLang.Library.Retry.randomAddresses log = [word w c] ∧
          if accept hash keys (sample rho c) then
            flow = .returned (sample rho c) ∧ Grouped (hash (sample rho c)) dir nodes keys.reverse mem' ∧ ArrayAt mem' input keys
          else ∃ out, flow = .next out ∧ I (c+1) n out mem') (300*(keys.length+m+1)+150) 34 := by
    rintro c n ls memory ⟨hc,hn,ha,seed,accepted,rfl⟩
    apply (iteration_contract p rho memory hash shift keys seed accepted hsample hroot hfill hfree
      hspace hlinear ha hhash hfit hdir hnodes hrandom hc (by omega)).consequence (work' := 300*(keys.length+m+1)+150) (peak' := 34)
    · rintro flow mem' log ⟨hp,hr,ha',hq⟩
      refine ⟨hp,hr,?_⟩
      cases hy : accept hash keys (sample rho c) with
      | true => simpa [hy,and_assoc] using And.intro hq ha'
      | false =>
        simp only [hy,Bool.false_eq_true,↓reduceIte] at hq ⊢
        exact ⟨_,hq,by dsimp [I]; exact ⟨by omega,by omega,ha',_,_,rfl⟩⟩
    · exact Nat.le_refl _
    · exact Nat.le_refl _
  have hi : I start total (locals input keys.length dir nodes m shift start total none none) mem :=
    ⟨Nat.le_refl _,Nat.le_refl _,hinput,none,none,rfl⟩
  obtain ⟨flow,mem',log,d,⟨hq,hp,hr⟩,ht,hs⟩ :=
    RamLang.Library.Search.loop_contract 7 iteration (sample rho) (accept hash keys) I
      (fun seed memory => Grouped (hash seed) dir nodes keys.reverse memory ∧ ArrayAt memory input keys)
      (policy input keys.length dir nodes m start total) (300*(keys.length+m+1)+150) 34
      counterValue trial start total _ mem hi
  cases he : RamLang.Library.Search.choice (sample rho) (accept hash keys) start total with
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

end PerfectHash.Source.Search.Root
