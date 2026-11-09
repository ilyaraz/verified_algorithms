import RamLang.DSL.Derive
import RamLang.Logic.EarlyReturn
import Algorithms.Dedup.Representation

namespace Dedup.Source.Search
open WordRam RamLang RamLang.Compiler RamLang.Logic
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- Search the existing one-based linked-node format. Full keys, including zero
and the maximum word, are compared as ordinary data. A hit returns immediately. -/
def program : RamLang.Program := ram_program find_key {
  fn find_key(nodes, cursor, key) {
    let pointer;
    let loaded;
    while (cursor != 0) {
      pointer = nodes + 2 * (cursor - 1);
      loaded = load(pointer);
      if (loaded == key) { return 1; }
      cursor = load(pointer + 1);
    }
    return 0;
  }
}

/-- Three parameters and five reusable locals occupy a ten-word frame. -/
def function : RamLang.Function := program.functions[0]'(by decide)

/-- Arbitrary old scratch locals, overwritten before they are read. -/
structure Scratch (w : Nat) where
  pointer : Option (Word w)
  loaded : Option (Word w)
  scaled : Option (Word w)
  subtract : Option (Word w)
  nextAddress : Option (Word w)

/-- Stable parameters and the current linked cursor, plus invocation-local scratch. -/
def locals (nodes cursor : Nat) (key : Word w) (old : Scratch w) : Locals w :=
  [some (word w nodes),some (word w cursor),some key,
    old.pointer,old.loaded,old.scaled,old.subtract,old.nextAddress]

/-- One probe, early match return, and following-link load. -/
def iteration : Stmt :=
  .seq (.primitive (.binary 6 .sub (.local 1) (.literal 1)))
    (.seq (.primitive (.binary 5 .mul (.literal 2) (.local 6)))
      (.seq (.primitive (.binary 3 .add (.local 0) (.local 5)))
        (.seq (.primitive (.load 4 (.local 3)))
          (.seq (.ite ⟨.eq,.local 4,.local 2⟩ (.ret (.literal 1)) .skip)
            (.seq (.primitive (.binary 7 .add (.local 3) (.literal 1)))
              (.primitive (.load 1 (.local 7))))))))

/-- The search loop tests the one-based cursor against its zero sentinel. -/
def loop : Stmt := .while ⟨.ne,.local 1,.literal 0⟩ iteration

/-- Source search only reads the reserved nodes. -/
def policy (nodes N : Nat) : AccessPolicy w := ⟨(Region.mk nodes (2*N)).Contains,fun _ => False,fun _ => False⟩

macro "search_test" : tactic => `(tactic|
  simp [Condition.eval,Atom.eval,requireSome,Comparison.test,Binary.eval,
    bind,pure,Except.bind,Except.pure,WordRam.word_add,WordRam.word_mul, *])

/-- One node probe implements full-key equality. The link is read only on a
miss; scratch locals are arbitrary, memory is unchanged, and reads stay local. -/
theorem iteration_contract {w free nodes N i : Nat} (p : RamLang.Program) (rho : RandomMemory w)
    (mem : DataMemory w) (key x : Word w) (rest : List (Word w × Nat)) (old : Scratch w)
    (hchain : ChainAt mem nodes ((x,i)::rest)) (hi : 0 < i) (hin : i ≤ N)
    (hf : (Region.mk nodes (2*N)).Fits w) :
    Contract p rho free iteration (locals nodes i key old) mem
      (fun flow mem' log => mem' = mem ∧ (policy nodes N).AllowsTrace log ∧
        if x = key then flow = .returned (word w 1)
        else ∃ saved, flow = .next (locals nodes (firstIndex rest) key saved)) 50 0 := by
  have hfit : nodes+2*N < modulus w := hf
  have hone : 1 < modulus w := by omega
  have hsub : word w i-word w 1 = word w (i-1) := WordRam.word_sub _ _ hone (by omega)
  obtain ⟨hk,hn,_⟩ := hchain
  simp only [nodeAddress] at hk hn
  obtain ⟨hkeyCell,hlinkCell⟩ := node_contains hf hi hin
  simp only [nodeAddress] at hkeyCell hlinkCell
  by_cases he : x = key
  · refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · simp [Binary.eval,hsub,WordRam.word_mul,WordRam.word_add,hk,he,
        policy,AccessPolicy.AllowsTrace,AccessPolicy.Allows,hkeyCell]
    · ram_cost
    · ram_cost
  · refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · simp only [Binary.eval,hsub,WordRam.word_mul,WordRam.word_add,hk,hn,he,↓reduceIte,
        true_and,eq_self_iff_true]
      constructor
      · simp [policy,AccessPolicy.AllowsTrace,AccessPolicy.Allows,hkeyCell,hlinkCell]
      · refine ⟨⟨_,_,_,_,_⟩,rfl⟩
    · ram_cost
    · ram_cost

/-- A loop either returns a witnessed match or reaches the sentinel after
proving the key absent from every node it was asked to search. -/
def Post (nodes : Nat) (key : Word w) (chain : List (Word w × Nat)) : Flow w → Prop
  | .returned value => value = word w 1 ∧ key ∈ chain.map Prod.fst
  | .next out => ∃ saved, out = locals nodes 0 key saved ∧ key ∉ chain.map Prod.fst
  | .exhausted => False

/-- A preceding unequal key does not change the result of searching the tail. -/
theorem Post.prepend_miss {nodes i : Nat} {key x : Word w} {chain : List (Word w × Nat)}
    {flow : Flow w} (he : x ≠ key) (h : Post nodes key chain flow) :
    Post nodes key ((x,i)::chain) flow := by
  cases flow <;> simpa [Post,Ne.symm he] using h

/-- A finite chain gives a source termination proof for the cursor loop. Its
work is bounded by the existing scanComparisons model, so early matches receive
only the probes actually performed rather than the entire bucket length. -/
theorem loop_contract {w free nodes N : Nat} (p : RamLang.Program) (rho : RandomMemory w)
    (mem : DataMemory w) (key : Word w) (chain : List (Word w × Nat)) (old : Scratch w)
    (hchain : ChainAt mem nodes chain) (hb : ∀ item ∈ chain, 0 < item.2 ∧ item.2 ≤ N)
    (hf : (Region.mk nodes (2*N)).Fits w) :
    Contract p rho free loop (locals nodes (firstIndex chain) key old) mem
      (fun flow mem' log => mem' = mem ∧ (policy nodes N).AllowsTrace log ∧ Post nodes key chain flow)
      (55*scanComparisons key (chain.map Prod.fst)+5) 0 := by
  induction chain generalizing old with
  | nil =>
    let d : Evaluation p rho free loop (locals nodes 0 key old) mem
        (.next (locals nodes 0 key old)) mem [] := .whileFalse (by rfl)
    exact Contract.ofEvaluation d ⟨rfl,by simp [AccessPolicy.AllowsTrace],old,rfl,by simp⟩
      (Nat.le_refl _) (Nat.le_refl _)
  | cons item rest ih =>
    obtain ⟨x,i⟩ := item
    obtain ⟨hpositive,hbound⟩ := hb (x,i) (by simp)
    have hfit : nodes+2*N < modulus w := hf
    have hi : i < modulus w := by omega
    have hzero : word w i ≠ word w 0 := by
      intro he
      have := (word_eq_iff_of_lt hi (by omega : 0 < modulus w)).mp he
      omega
    have htest : (Condition.mk .ne (.local 1) (.literal 0)).eval (locals nodes i key old) = .ok true := by
      simp [Condition.eval,Atom.eval,requireSome,Comparison.test,locals,hzero,
        bind,pure,Except.bind,Except.pure]
    obtain ⟨flow,mem',log,d,⟨hmem,hpolicy,hpost⟩,ht,hpeak⟩ :=
      iteration_contract p rho mem key x rest old hchain hpositive hbound hf
    subst mem'
    by_cases he : x = key
    · rw [if_pos he] at hpost
      subst flow
      refine Contract.ofEvaluation (.whileStop htest d (by trivial))
        ⟨rfl,hpolicy,by simp [Post,he]⟩ ?_ (by simpa only [extraStack] using hpeak)
      simp only [List.map_cons,Prod.fst,scanComparisons,show key = x from he.symm,↓reduceIte]
      change 4+instructions d ≤ 55*1+5
      omega
    · rw [if_neg he] at hpost
      obtain ⟨saved,hflow⟩ := hpost
      subst flow
      obtain ⟨flow,mem',suffix,tail,⟨hmem',hpolicy',hpost'⟩,ht',hpeak'⟩ :=
        ih saved hchain.2.2 (fun item hm => hb item (List.mem_cons_of_mem _ hm))
      subst mem'
      refine Contract.ofEvaluation (.whileContinue htest d tail)
        ⟨rfl,(AccessPolicy.allowsTrace_append _).mpr ⟨hpolicy,hpolicy'⟩,hpost'.prepend_miss he⟩ ?_ ?_
      · simp only [List.map_cons,Prod.fst,scanComparisons,Ne.symm he,↓reduceIte]
        change 5+instructions d+instructions tail ≤ 55*(1+scanComparisons key (rest.map Prod.fst))+5
        omega
      · exact Nat.max_le.mpr ⟨hpeak,hpeak'⟩

/-- Complete callable search returns the exact zero/one membership flag, leaves
application memory unchanged, and costs at most 55 instructions per actual key
comparison plus twelve fixed instructions. It allocates no nested frame. -/
theorem contract {w free nodes N : Nat} (p : RamLang.Program) (rho : RandomMemory w)
    (mem : DataMemory w) (key : Word w) (chain : List (Word w × Nat))
    (hchain : ChainAt mem nodes chain) (hb : ∀ item ∈ chain, 0 < item.2 ∧ item.2 ≤ N)
    (hf : (Region.mk nodes (2*N)).Fits w) :
    Contract p rho free function.body
      ([word w nodes,word w (firstIndex chain),key].map some ++ List.replicate function.locals.length none) mem
      (fun flow mem' log => flow = .returned (word w (if key ∈ chain.map Prod.fst then 1 else 0)) ∧
        mem' = mem ∧ (policy nodes N).AllowsTrace log)
      (55*scanComparisons key (chain.map Prod.fst)+12) 0 := by
  obtain ⟨flow,mem',log,d,⟨hmem,hpolicy,hpost⟩,ht,hpeak⟩ :=
    loop_contract (free := free) p rho mem key chain ⟨none,none,none,none,none⟩ hchain hb hf
  subst mem'
  cases flow with
  | next out =>
    obtain ⟨saved,rfl,habsent⟩ := hpost
    refine Contract.ofEvaluation (.sequence d (.ret (atom := .literal 0) rfl))
      ⟨by simp [habsent],rfl,by simpa using hpolicy⟩ ?_ ?_
    · change instructions d+7 ≤ 55*scanComparisons key (chain.map Prod.fst)+12
      omega
    · simpa only [extraStack,Nat.max_zero] using hpeak
  | returned value =>
    obtain ⟨rfl,hpresent⟩ := hpost
    refine Contract.ofEvaluation (.sequenceStop d (by trivial)) ⟨by simp [hpresent],rfl,hpolicy⟩ ?_ ?_
    · change instructions d ≤ 55*scanComparisons key (chain.map Prod.fst)+12
      omega
    · exact hpeak
  | exhausted => exact False.elim hpost

end Dedup.Source.Search
