import RamLang.DSL.Derive
import RamLang.Library.Fill
import RamLang.Logic.Reprogram
import DataStructures.PerfectHash.Construction.Slots
import Algorithms.Dedup.Representation

namespace PerfectHash.Source.Child
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Construction
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- A child trial clears only its own table, follows the existing linked-node
format and rejects on the first occupied slot. Flags keep zero keys distinct
from empty slots. The shared clearing routine is called normally. -/
def program : RamLang.Program := ram_program main {
  fn main(configuration, seed, shift) {
    let nodes = load(configuration);
    let cursor = load(configuration + 1);
    let table = load(configuration + 2);
    let slots = load(configuration + 3);
    return child(nodes, cursor, table, slots, seed, shift);
  }
  fn child(nodes, cursor, table, slots, seed, shift) {
    fill(table, 2 * slots, 0);
    while (cursor != 0) {
      let node = nodes + 2 * (cursor - 1);
      let key = load(node);
      let index = (seed * key) >> shift;
      let slot = table + 2 * index;
      let occupied = load(slot);
      if (occupied != 0) { return 0; }
      store(slot, 1);
      store(slot + 1, key);
      cursor = load(node + 1);
    }
    return 1;
  }
  fn fill(p, n, value) {
    while (n != 0) { store(p, value); p = p + 1; n = n - 1; }
    return 0;
  }
}

/-- The callable child trial shares the fixed clearing-helper identifier two. -/
def function : RamLang.Function := program.functions[1]'(by decide)

/-- The helper body is the already verified generic fill implementation. -/
theorem fill_eq : program.functions[2]? = some RamLang.Logic.Fill.function := rfl

/-- The source loop selected from the checked DSL function. -/
def loop : Stmt := match function.body with
  | .seq _ (.seq _ (.seq body _)) => body | _ => .skip

/-- A single collision check and, on success, insertion and link traversal. -/
def iteration : Stmt := match loop with | .while _ body => body | _ => .skip

/-- Thirteen fixed scratch slots may retain arbitrary values between probes. -/
abbrev Scratch (w : Nat) := Fin 13 → Option (Word w)

/-- The six stable parameters and the compiler's scratch slots. -/
def locals (nodes cursor table q : Nat) (seed shift : Word w) (old : Scratch w) : Locals w :=
  [some (word w nodes),some (word w cursor),some (word w table),some (word w q),some seed,some shift,
    old 0, old 1, old 2, old 3, old 4, old 5, old 6, old 7, old 8, old 9, old 10, old 11, old 12]

/-- A trial may read linked nodes and its table but may write only its table.
This policy excludes every already completed sibling table. -/
def policy (nodes N table q : Nat) : AccessPolicy w :=
  ⟨fun a => (Region.mk nodes (2*N)).Contains a ∨ (Region.mk table (2*q)).Contains a,
   (Region.mk table (2*q)).Contains,fun _ => False⟩

macro "child_test" : tactic => `(tactic|
  simp [Condition.eval,Atom.eval,requireSome,Comparison.test,Binary.eval,
    bind,pure,Except.bind,Except.pure,WordRam.word_add,WordRam.word_mul, *] <;> omega)

/-- A probe rejects exactly when the mathematical slot is occupied. Otherwise
its two writes implement slotMemory and leave the linked chain unchanged. -/
theorem iteration_contract {w free nodes N table q i : Nat} (p : RamLang.Program)
    (rho : RandomMemory w) (mem : DataMemory w) (hash : Word w → Nat)
    (seed shift key : Word w) (seen : List (Word w)) (rest : List (Word w × Nat)) (old : Scratch w)
    (hslots : SlotsAt hash q table seen mem) (hchain : Dedup.ChainAt mem nodes ((key,i)::rest))
    (hi : 0 < i) (hin : i ≤ N) (hh : hash key < q)
    (hhash : unsignedShiftRight (seed*key) shift = word w (hash key))
    (hnode : (Region.mk nodes (2*N)).Fits w) (htable : (Region.mk table (2*q)).Fits w)
    (hsep : (Region.mk nodes (2*N)).Separated ⟨table,2*q⟩) :
    Contract p rho free iteration (locals nodes i table q seed shift old) mem
      (fun flow mem' log => (policy nodes N table q).AllowsTrace log ∧
        if hash key ∈ seen.map hash then flow = .returned (word w 0) ∧ mem' = mem
        else mem' = slotMemory table (hash key) key mem ∧
          ∃ saved, flow = .next (locals nodes (Dedup.firstIndex rest) table q seed shift saved)) 150 0 := by
  have hnfit : nodes+2*N < modulus w := hnode
  have hone : 1 < modulus w := by omega
  have hsub : word w i-word w 1 = word w (i-1) := WordRam.word_sub _ _ hone hi
  obtain ⟨hkey,hnext,_⟩ := hchain
  simp only [Dedup.nodeAddress] at hkey hnext
  obtain ⟨hn₀,hn₁⟩ := Dedup.node_contains hnode hi hin
  simp only [Dedup.nodeAddress] at hn₀ hn₁
  have ht₀ := Region.contains_index htable (by omega : 2*hash key < 2*q)
  have ht₁ := Region.contains_index htable (by omega : 2*hash key+1 < 2*q)
  simp only [← Nat.add_assoc] at ht₁
  have hnext' : update (update mem (word w (table+2*hash key)) (word w 1))
      (word w (table+2*hash key+1)) key (word w (nodes+2*(i-1)+1)) = word w (Dedup.firstIndex rest) :=
    (slotMemory_frame (mem := mem) (x := key) htable hh _
      (Region.not_contains_of_separated hsep hn₁)).trans hnext
  have hempty := hslots.empty_iff hone hh
  by_cases he : hash key ∈ seen.map hash
  · have hflag : mem (word w (table+2*hash key)) ≠ word w 0 := by
      intro h
      exact (hempty.mp h) he
    refine ⟨_,_,_,by ram_derive (child_test),?_,?_,?_⟩
    · simp [Binary.eval,hsub,WordRam.word_mul,WordRam.word_add,hkey,hhash,he,
        policy,AccessPolicy.AllowsTrace,AccessPolicy.Allows,hn₀,ht₀]
    · ram_cost
    · ram_cost
  · have hflag := hempty.mpr he
    refine ⟨_,_,_,by ram_derive (child_test),?_,?_,?_⟩
    · simp only [Binary.eval,hsub,WordRam.word_mul,WordRam.word_add,hkey,hhash,hnext',he,↓reduceIte]
      constructor
      · simp [policy,AccessPolicy.AllowsTrace,AccessPolicy.Allows,hn₀,hn₁,ht₀,ht₁,← Nat.add_assoc]
      · constructor
        · rfl
        · refine ⟨![_,_,_,_,_,_,_,_,_,_,_,_,_],rfl⟩
    · ram_cost
    · ram_cost

/-- Loop success establishes the exact slot model for all accepted keys;
failure is the model's first collision, represented by an ordinary zero return. -/
def Post (hash : Word w → Nat) (nodes table q : Nat) (seed shift : Word w)
    (seen : List (Word w)) (chain : List (Word w × Nat)) (flow : Flow w) (mem : DataMemory w) : Prop :=
  if childAccepted hash seen (chain.map Prod.fst) then
    ∃ saved, flow = .next (locals nodes 0 table q seed shift saved) ∧
      SlotsAt hash q table ((chain.map Prod.fst).reverse++seen) mem
  else flow = .returned (word w 0)

/-- The concrete cursor loop agrees with childAccepted on every linked list,
including rejected trials. Its write policy preserves all other tables and the
node list, and its numerical bound includes each actual loop test. -/
theorem loop_contract {w free nodes N table q : Nat} (p : RamLang.Program)
    (rho : RandomMemory w) (mem : DataMemory w) (hash : Word w → Nat)
    (seed shift : Word w) (seen : List (Word w)) (chain : List (Word w × Nat)) (old : Scratch w)
    (hslots : SlotsAt hash q table seen mem) (hchain : Dedup.ChainAt mem nodes chain)
    (hb : ∀ item ∈ chain, 0 < item.2 ∧ item.2 ≤ N)
    (hh : ∀ key, hash key < q)
    (hhash : ∀ key, unsignedShiftRight (seed*key) shift = word w (hash key))
    (hnode : (Region.mk nodes (2*N)).Fits w) (htable : (Region.mk table (2*q)).Fits w)
    (hsep : (Region.mk nodes (2*N)).Separated ⟨table,2*q⟩) :
    Contract p rho free loop (locals nodes (Dedup.firstIndex chain) table q seed shift old) mem
      (fun flow mem' log => (policy nodes N table q).AllowsTrace log ∧
        Post hash nodes table q seed shift seen chain flow mem') (155*chain.length+5) 0 := by
  induction chain generalizing mem seen old with
  | nil =>
    exact Contract.ofEvaluation (.whileFalse (by rfl))
      ⟨by simp [AccessPolicy.AllowsTrace],by simpa [Post,childAccepted,Dedup.firstIndex] using
        (show ∃ s, Flow.next (locals nodes 0 table q seed shift old) =
          .next (locals nodes 0 table q seed shift s) ∧ SlotsAt hash q table seen mem from ⟨old,rfl,hslots⟩)⟩
      (Nat.le_refl _) (Nat.le_refl _)
  | cons item rest ih =>
    obtain ⟨key,i⟩ := item
    obtain ⟨hi,hin⟩ := hb (key,i) (by simp)
    have hnf : nodes+2*N < modulus w := hnode
    have hzero : word w i ≠ word w 0 := by
      intro he
      have := (word_eq_iff_of_lt (by omega : i < modulus w) (by omega : 0 < modulus w)).mp he
      omega
    have htest : (Condition.mk .ne (.local 1) (.literal 0)).eval (locals nodes i table q seed shift old) = .ok true := by
      simp [Condition.eval,Atom.eval,requireSome,Comparison.test,locals,hzero,bind,pure,Except.bind,Except.pure]
    obtain ⟨flow,mem',log,d,⟨hp,hpost⟩,ht,hs⟩ :=
      iteration_contract (free := free) p rho mem hash seed shift key seen rest old hslots hchain hi hin
        (hh key) (hhash key) hnode htable hsep
    by_cases he : hash key ∈ seen.map hash
    · rw [if_pos he] at hpost
      obtain ⟨hflow,_⟩ := hpost
      subst flow
      refine Contract.ofEvaluation (.whileStop htest d (by trivial))
        ⟨hp,by simp [Post,childAccepted,he]⟩ ?_ (by simpa only [extraStack] using hs)
      change 4+instructions d ≤ 155*(rest.length+1)+5
      omega
    · rw [if_neg he] at hpost
      obtain ⟨hm,saved,hflow⟩ := hpost
      have hslots' : SlotsAt hash q table (key::seen) mem' := by
        rw [hm]
        exact hslots.insert htable (hh key)
      have hbound : ∀ item ∈ rest, 0 < item.2 ∧ item.2 ≤ N :=
        fun item hm => hb item (List.mem_cons_of_mem _ hm)
      have hchain' : Dedup.ChainAt mem' nodes rest :=
        hchain.2.2.frame hbound hnode (fun a ha =>
          (d.frame_of_policy hp (Region.not_contains_of_separated hsep ha)).symm)
      subst flow
      obtain ⟨flow,mem'',suffix,tail,⟨hp',hq'⟩,ht',hs'⟩ := ih mem' (key::seen) saved hslots' hchain' hbound
      refine Contract.ofEvaluation (.whileContinue htest d tail)
        ⟨(AccessPolicy.allowsTrace_append _).mpr ⟨hp,hp'⟩,?_⟩ ?_ ?_
      · simpa [Post,childAccepted,he,List.reverse_cons,List.append_assoc] using hq'
      · change 5+instructions d+instructions tail ≤ 155*(rest.length+1)+5
        omega
      · exact Nat.max_le.mpr ⟨hs,hs'⟩

/-- Initial loop locals after the shared clear routine returns zero. -/
def initialLocals (nodes cursor table q : Nat) (seed shift : Word w) : Locals w :=
  [some (word w nodes),some (word w cursor),some (word w table),some (word w q),some seed,some shift,
    some (word w 0),some (word w 2*word w q)] ++ List.replicate 11 none

/-- Complete child trial: dirty flags are initialized, rejection matches the
existing collision predicate, and success establishes the complete slot model.
The five-word fill frame is the only nested allocation. -/
theorem contract {w free nodes N table q : Nat} (p : RamLang.Program)
    (rho : RandomMemory w) (mem : DataMemory w) (hash : Word w → Nat)
    (seed shift : Word w) (chain : List (Word w × Nat))
    (hlookup : p.functions[2]? = some RamLang.Logic.Fill.function) (hfree : 5 ≤ free)
    (hchain : Dedup.ChainAt mem nodes chain) (hb : ∀ item ∈ chain, 0 < item.2 ∧ item.2 ≤ N)
    (hh : ∀ key, hash key < q)
    (hhash : ∀ key, unsignedShiftRight (seed*key) shift = word w (hash key))
    (hnode : (Region.mk nodes (2*N)).Fits w) (htable : (Region.mk table (2*q)).Fits w)
    (hsep : (Region.mk nodes (2*N)).Separated ⟨table,2*q⟩) :
    Contract p rho free function.body
      ([word w nodes,word w (Dedup.firstIndex chain),word w table,word w q,seed,shift].map some ++
        List.replicate function.locals.length none) mem
      (fun flow mem' log => flow = .returned (word w (if childAccepted hash [] (chain.map Prod.fst) then 1 else 0)) ∧
        (childAccepted hash [] (chain.map Prod.fst) = true → SlotsAt hash q table (chain.map Prod.fst).reverse mem') ∧
        (policy nodes N table q).AllowsTrace log) (200*(q+chain.length+1)) 5 := by
  let cleared := RamLang.Logic.Fill.filled mem table (2*q) (word w 0)
  have hc := (RamLang.Library.Fill.contract (free := free-5) rho mem table (2*q) (word w 0)
    htable).reprogram p (by repeat constructor)
  have hc' : Contract p rho (free-5) RamLang.Logic.Fill.function.body
      [some (word w table),some (word w 2*word w q),some (word w 0)] mem
      (fun flow mem' log => flow = .returned (word w 0) ∧ mem' = cleared ∧
        (RamLang.Logic.Fill.policy table (2*q)).AllowsTrace log) (22*(2*q)+12) 0 := by
    simpa only [WordRam.word_mul] using hc
  obtain ⟨flow,mem₁,log₁,clear,⟨hf,hm,hp₁⟩,ht₁,hs₁⟩ := hc'
  subst flow
  subst mem₁
  have hchain' : Dedup.ChainAt cleared nodes chain :=
    hchain.frame hb hnode (fun a ha => (RamLang.Logic.Fill.filled_outside mem table (2*q) (word w 0) a
      (Region.not_contains_of_separated hsep ha)).symm)
  have hslots : SlotsAt hash q table [] cleared :=
    SlotsAt.empty (RamLang.Logic.Fill.filled_array mem table (2*q) (word w 0) htable)
  have hl := loop_contract (free := free) p rho cleared hash seed shift [] chain
    ![some (word w 0),some (word w 2*word w q),none,none,none,none,none,none,none,none,none,none,none]
    hslots hchain' hb hh hhash hnode htable hsep
  have hl' : Contract p rho free loop (initialLocals nodes (Dedup.firstIndex chain) table q seed shift) cleared
      (fun flow mem' log => (policy nodes N table q).AllowsTrace log ∧
        Post hash nodes table q seed shift [] chain flow mem') (155*chain.length+5) 0 := by
    simpa [initialLocals,locals] using hl
  obtain ⟨flow,mem₂,log₂,body,⟨hp₂,hq⟩,ht₂,hs₂⟩ := hl'
  have hp₁' : (policy nodes N table q).AllowsTrace log₁ := by
    intro e he
    have hh := hp₁ e he
    cases e with
    | dataRead => exact False.elim hh
    | randomRead => exact False.elim hh
    | dataWrite => exact hh
  cases he : childAccepted hash [] (chain.map Prod.fst) with
  | false =>
    simp only [Post,he,Bool.false_eq_true,↓reduceIte] at hq
    subst flow
    refine ⟨_,_,_,by ram_derive (child_test),?_,?_,?_⟩
    · simpa [he,AccessPolicy.allowsTrace_append] using And.intro hp₁' hp₂
    · ram_cost
      omega
    · ram_cost
      change 5+extraStack clear ≤ 5 ∧ extraStack body ≤ 5
      omega
  | true =>
    simp only [Post,he,↓reduceIte,List.append_nil] at hq
    obtain ⟨saved,hflow,hslots'⟩ := hq
    subst flow
    refine ⟨_,_,_,by ram_derive (child_test),?_,?_,?_⟩
    · simpa [he,AccessPolicy.allowsTrace_append] using And.intro hslots' (And.intro hp₁' hp₂)
    · ram_cost
      omega
    · ram_cost
      change 5+extraStack clear ≤ 5 ∧ extraStack body ≤ 5
      omega

end PerfectHash.Source.Child
