import Algorithms.Dedup.Source.Search
import Algorithms.Dedup.Insertion
import RamLang.Library.Fill
import RamLang.Logic.Reprogram
import Hashing.Source.Sampling

namespace Dedup.Source.Pass
open WordRam RamLang RamLang.Compiler RamLang.Logic
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- Deduplicate an array using bucket chains and full-key comparison. The caller
supplies sampled hash parameters; all head initialization, searches, node stores
and compact-output writes are executed here through ordinary source operations. -/
def program : RamLang.Program := ram_program main {
  fn main(configuration, seed, shift) {
    let input = load(configuration);
    let count = load(configuration + 1);
    let scratch = load(configuration + 2);
    let buckets = load(configuration + 3);
    return deduplicate(input, count, scratch, buckets, seed, shift);
  }
  fn deduplicate(input, count, scratch, buckets, seed, shift) {
    let nodes = scratch + 2 * (count + 1);
    let compact = nodes + 2 * count;
    let distinct = 0;
    fill(scratch, buckets, 0);
    while (count != 0) {
      let key = load(input);
      let bucket = (seed * key) >> shift;
      let headCell = scratch + bucket;
      let head = load(headCell);
      let found = find_key(nodes, head, key);
      if (found == 0) {
        let node = nodes + 2 * distinct;
        store(node, key);
        store(node + 1, head);
        store(compact + distinct, key);
        store(headCell, distinct + 1);
        distinct = distinct + 1;
      }
      input = input + 1;
      count = count - 1;
    }
    return distinct;
  }
  fn fill(p, n, value) {
    while (n != 0) { store(p, value); p = p + 1; n = n - 1; }
    return 0;
  }
  fn sample_seed(address) {
    let raw = random(address);
    return raw - raw % 2 + 1;
  }
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

/-- Callable deduplication pass using the shared fill and search identifiers. -/
def function : RamLang.Function := program.functions[1]'(by decide)

/-- Both called helpers are the reusable functions with established contracts. -/
theorem helpers : program.functions[2]? = some RamLang.Logic.Fill.function ∧
    program.functions[4]? = some Dedup.Source.Search.function := by constructor <;> rfl

/-- The loop selected from the checked DSL pass. -/
def loop : Stmt := match function.body with
  | .seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq _ (.seq body _))))))) => body
  | _ => .skip

/-- One hash, chain search, optional insertion, and input advance. -/
def iteration : Stmt := match loop with | .while _ body => body | _ => .skip

/-- Fifteen fixed scratch slots include lowered expression temporaries. -/
abbrev Scratch (w : Nat) := Fin 15 → Option (Word w)

/-- Known loop values and arbitrary invocation-local scratch. -/
def locals (l : Layout) (N input remaining m distinct : Nat) (seed shift : Word w)
    (old : Scratch w) : Locals w :=
  [some (word w input),some (word w remaining),some (word w l.scratch),some (word w m),some seed,some shift,
   some (word w (l.nodes N).base),old 0,old 1,some (word w (l.compact N).base),old 2,
   some (word w distinct),old 3,old 4,old 5,old 6,old 7,old 8,old 9,old 10,old 11,old 12,old 13,old 14]

/-- Deduplication reads the input and workspace and writes only its workspace. -/
def policy (l : Layout) (N : Nat) : AccessPolicy w :=
  ⟨fun a => (l.inputRegion N).Contains a ∨ (l.workspace N).Contains a,
   (l.workspace N).Contains,fun _ => False⟩

macro "dedup_test" : tactic => `(tactic|
  simp [Condition.eval,Atom.eval,requireSome,Comparison.test,Binary.eval,
    bind,pure,Except.bind,Except.pure,WordRam.word_add,WordRam.word_mul, *] <;> omega)

/-- A single input step calls the verified full-key search and agrees with
seed-independent insert. Only genuinely new keys allocate a node and compact
word. The search's actual comparison model remains visible in the time bound. -/
theorem iteration_contract {w free N input remaining m : Nat} (p : RamLang.Program)
    (rho : RandomMemory w) (mem : DataMemory w) (l : Layout) (hash : Word w → Nat)
    (seed shift key : Word w) (seen : List (Word w)) (old : Scratch w)
    (hlookup : p.functions[4]? = some Dedup.Source.Search.function) (hfree : 10 ≤ free)
    (ha : Admissible w N l) (hm : m ≤ 2*(N+1)) (hh : hash key < m)
    (hhash : unsignedShiftRight (seed*key) shift = word w (hash key))
    (hrep : Representation w N l m hash seen mem) (hlen : seen.length < N)
    (hr : 0 < remaining) (hkey : mem (word w input) = key)
    (hread : (l.inputRegion N).Contains (word w input)) :
    Contract p rho free iteration (locals l N input remaining m seen.length seed shift old) mem
      (fun flow mem' log => (policy l N).AllowsTrace log ∧
        mem' = (if key ∈ seen then mem else insertMemory l N seen.length (hash key) key
          (word w (firstIndex (chain hash seen (hash key)))) mem) ∧
        ∃ saved, flow = .next (locals l N (input+1) (remaining-1) m (insert key seen).length seed shift saved))
      (220+55*scanComparisons key (bucket hash seen key)) 10 := by
  have hhead := hrep.head (hash key) hh
  have hchain := hrep.chains (hash key) hh
  have hc := Search.contract (free := free-10) p rho mem key (chain hash seen (hash key)) hchain
    (fun item hi => by obtain ⟨key,i⟩ := item; have hb := chain_index hi; exact ⟨hb.1,by omega⟩) ha.nodes_fit
  have hc' : Contract p rho (free-10) Search.function.body
      ([word w (l.nodes N).base,
        mem (word w l.scratch+unsignedShiftRight (seed*mem (word w input)) shift),mem (word w input)].map some ++
        List.replicate Search.function.locals.length none) mem
      (fun flow mem' log => flow = .returned (word w (if key ∈ seen then 1 else 0)) ∧
        mem' = mem ∧ (Search.policy (l.nodes N).base N).AllowsTrace log)
      (55*scanComparisons key (bucket hash seen key)+12) 0 := by
    simpa [hkey,hhash,WordRam.word_add,hhead,chain_keys,bucket] using hc
  obtain ⟨flow,mem',log,search,⟨hf,hmem,hp⟩,ht,hs⟩ := hc'
  subst flow
  subst mem'
  have hfwork : l.scratch+6*(N+1) < modulus w := ha.workspace
  have hbkt : hash key < 2*(N+1) := by omega
  have hheadCell : (l.workspace N).Contains (word w (l.scratch+hash key)) :=
    Region.contains_index ha.workspace (by change hash key < 6*(N+1); omega)
  have hnode₀ : (l.workspace N).Contains (word w ((l.nodes N).base+2*seen.length)) := by
    simpa [Layout.nodes,Nat.add_assoc] using
      (Region.contains_index ha.workspace (by change 2*(N+1)+2*seen.length < 6*(N+1); omega))
  have hnode₁ : (l.workspace N).Contains (word w ((l.nodes N).base+2*seen.length+1)) := by
    simpa [Layout.nodes,Nat.add_assoc] using
      (Region.contains_index ha.workspace (by change 2*(N+1)+2*seen.length+1 < 6*(N+1); omega))
  have hcompact : (l.workspace N).Contains (word w ((l.compact N).base+seen.length)) := by
    simpa [Layout.compact,Nat.add_assoc] using
      (Region.contains_index ha.workspace (by change 2*(N+1)+(2*N+seen.length) < 6*(N+1); omega))
  have hsearch : (policy l N).AllowsTrace log := by
    intro e he
    have h := hp e he
    cases e with
    | dataRead a value =>
      apply Or.inr
      change (l.nodes N).base ≤ a.toNat ∧ a.toNat < (l.nodes N).base+2*N at h
      simp only [Layout.nodes] at h
      change l.scratch ≤ a.toNat ∧ a.toNat < l.scratch+6*(N+1)
      omega
    | dataWrite => exact False.elim h
    | randomRead => exact False.elim h
  have hone : 1 < modulus w := by omega
  have hsub : word w remaining-word w 1 = word w (remaining-1) := WordRam.word_sub _ _ hone hr
  have hzero : word w 1 ≠ word w 0 := by
    intro he
    have := (word_eq_iff_of_lt hone (by omega : 0 < modulus w)).mp he
    omega
  by_cases he : key ∈ seen
  · refine ⟨_,_,_,by ram_derive (dedup_test),?_,?_,?_⟩
    · simp only [Binary.eval,hkey,hhash,WordRam.word_add,WordRam.word_mul,hhead,hsub,he,↓reduceIte]
      constructor
      · simp only [List.nil_append,List.append_nil,AccessPolicy.allowsTrace_append,hsearch,true_and,and_true]
        simp [policy,AccessPolicy.AllowsTrace,AccessPolicy.Allows,hread,hheadCell]
      · constructor
        · trivial
        · simp only [insert,if_pos he]
          exact ⟨![_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],rfl⟩
    · ram_cost
      omega
    · ram_cost
      change 10+extraStack search ≤ 10
      omega
  · refine ⟨_,_,_,by ram_derive (dedup_test),?_,?_,?_⟩
    · simp only [Binary.eval,hkey,hhash,WordRam.word_add,WordRam.word_mul,hhead,hsub,he,↓reduceIte]
      constructor
      · simp only [List.nil_append,List.append_nil,AccessPolicy.allowsTrace_append,hsearch,true_and,and_true]
        simp [policy,AccessPolicy.AllowsTrace,AccessPolicy.Allows,hread,hheadCell,hnode₀,hnode₁,hcompact]
      · constructor
        · rfl
        · simp only [insert,if_neg he,List.length_cons]
          exact ⟨![_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],rfl⟩
    · ram_cost
      omega
    · ram_cost
      change 10+extraStack search ≤ 10
      omega

/-- The deduplication loop follows the seed-independent collect model and its
seed-dependent comparison count. Input preservation follows from its write
policy, without assuming any workspace word initially contains zero. -/
theorem loop_contract {w free N input m : Nat} (p : RamLang.Program)
    (rho : RandomMemory w) (mem : DataMemory w) (l : Layout) (hash : Word w → Nat)
    (seed shift : Word w) (seen rest : List (Word w)) (old : Scratch w)
    (hlookup : p.functions[4]? = some Search.function) (hfree : 10 ≤ free)
    (ha : Admissible w N l) (hm : m ≤ 2*(N+1)) (hh : ∀ key, hash key < m)
    (hhash : ∀ key, unsignedShiftRight (seed*key) shift = word w (hash key))
    (hrep : Representation w N l m hash seen mem) (hlen : seen.length+rest.length ≤ N)
    (hinput : ArrayAt mem input rest) (hstart : l.input ≤ input) (hend : input+rest.length ≤ l.input+N) :
    Contract p rho free loop (locals l N input rest.length m seen.length seed shift old) mem
      (fun flow mem' log => (policy l N).AllowsTrace log ∧ Representation w N l m hash (collect rest seen) mem' ∧
        ∃ saved, flow = .next (locals l N (input+rest.length) 0 m (collect rest seen).length seed shift saved))
      (225*rest.length+55*comparisons hash rest seen+5) 10 := by
  induction rest generalizing input seen mem old with
  | nil =>
    refine Contract.ofEvaluation (.whileFalse (by rfl))
      ⟨by simp [AccessPolicy.AllowsTrace],hrep,old,by simp [collect]⟩ (Nat.le_refl _) ?_
    change 0 ≤ 10
    decide
  | cons key rest ih =>
    have hn : seen.length < N := by simp only [List.length_cons] at hlen; omega
    have hi : l.input+N < modulus w := ha.input
    have hc : rest.length+1 < modulus w := by simp only [List.length_cons] at hlen; omega
    have hzero : word w (rest.length+1) ≠ word w 0 := by
      intro he
      have := (word_eq_iff_of_lt hc (by omega : 0 < modulus w)).mp he
      omega
    have htest : (Condition.mk .ne (.local 1) (.literal 0)).eval
        (locals l N input (key::rest).length m seen.length seed shift old) = .ok true := by
      simp [Condition.eval,Atom.eval,requireSome,Comparison.test,locals,hzero,bind,pure,Except.bind,Except.pure]
    have hread : (l.inputRegion N).Contains (word w input) := by
      simp only [List.length_cons] at hend
      change l.input ≤ (word w input).toNat ∧ (word w input).toNat < l.input+N
      rw [word_toNat_of_lt (by omega : input < modulus w)]
      omega
    obtain ⟨hkey,htail⟩ := arrayAt_cons.mp hinput
    obtain ⟨flow,mem',log,d,⟨hp,hmem,saved,hflow⟩,ht,hs⟩ :=
      iteration_contract (free := free) (remaining := rest.length+1) p rho mem l hash seed shift key seen old
        hlookup hfree ha hm (hh key) (hhash key) hrep hn (by omega) hkey hread
    have hrep' : Representation w N l m hash (insert key seen) mem' := by
      rw [hmem]
      by_cases he : key ∈ seen
      · simpa [insert,he] using hrep
      · simpa [insert,he] using hrep.insertMemory ha hm (hh key) he hn
    have hinput' : ArrayAt mem' (input+1) rest := by
      intro i
      rw [d.frame_of_policy hp]
      · exact htail i
      · have hh : (l.inputRegion N).Contains (word w (input+1+i.val)) := by
          have hb := i.isLt
          simp only [List.length_cons] at hend
          change l.input ≤ (word w (input+1+i.val)).toNat ∧ (word w (input+1+i.val)).toNat < l.input+N
          rw [word_toNat_of_lt (by omega : input+1+i.val < modulus w)]
          omega
        exact Region.not_contains_of_separated ha.separated hh
    have hflow' : flow = .next (locals l N (input+1) rest.length m (insert key seen).length seed shift saved) :=
      by simpa using hflow
    subst flow
    obtain ⟨flow,mem'',suffix,tail,⟨hp',hrep'',saved',hflow'⟩,ht',hs'⟩ :=
      ih (input := input+1) mem' (insert key seen) saved hrep'
        (by have := insert_length (key := key) (seen := seen); simp only [List.length_cons] at hlen; omega)
        hinput' (by omega) (by simp only [List.length_cons] at hend; omega)
    refine Contract.ofEvaluation (.whileContinue htest d tail)
      ⟨(AccessPolicy.allowsTrace_append _).mpr ⟨hp,hp'⟩,hrep'',saved',?_⟩ ?_ ?_
    · simpa [collect,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hflow'
    · change 5+instructions d+instructions tail ≤
        225*(rest.length+1)+55*(scanComparisons key (bucket hash seen key)+comparisons hash rest (insert key seen))+5
      omega
    · exact Nat.max_le.mpr ⟨hs,hs'⟩

/-- Raw loop locals after computing the layout and clearing all head cells. -/
def initialLocals (l : Layout) (N m : Nat) (seed shift : Word w) : Locals w :=
  [some (word w l.input),some (word w N),some (word w l.scratch),some (word w m),some seed,some shift,
   some (word w l.scratch+word w 2*(word w N+word w 1)),some (word w 2*(word w N+word w 1)),
   some (word w N+word w 1),
   some (word w l.scratch+word w 2*(word w N+word w 1)+word w 2*word w N),some (word w 2*word w N),
   some (word w 0),some (word w 0)] ++ List.replicate 11 none

/-- Complete callable deduplication produces the exact compact distinct-key
sequence and linked-bucket representation. Sampling and rounding are separate
reusable calls, so their probability and costs are composed by the constructor. -/
theorem contract {w free N m : Nat} (p : RamLang.Program) (rho : RandomMemory w)
    (mem : DataMemory w) (l : Layout) (hash : Word w → Nat) (seed shift : Word w) (keys : List (Word w))
    (hfill : p.functions[2]? = some RamLang.Logic.Fill.function)
    (hsearch : p.functions[4]? = some Search.function) (hfree : 10 ≤ free)
    (ha : Admissible w N l) (hm : m ≤ 2*(N+1)) (hh : ∀ key, hash key < m)
    (hhash : ∀ key, unsignedShiftRight (seed*key) shift = word w (hash key))
    (hlen : keys.length = N) (hinput : ArrayAt mem l.input keys) :
    Contract p rho free function.body
      ([word w l.input,word w N,word w l.scratch,word w m,seed,shift].map some ++
        List.replicate function.locals.length none) mem
      (fun flow mem' log => flow = .returned (word w (collect keys []).length) ∧
        Representation w N l m hash (collect keys []) mem' ∧ (policy l N).AllowsTrace log)
      (300*(N+m+1)+55*comparisons hash keys []) 10 := by
  have hfwork : l.scratch+6*(N+1) < modulus w := ha.workspace
  have hmfit : l.scratch+m < modulus w := by omega
  let cleared := RamLang.Logic.Fill.filled mem l.scratch m (word w 0)
  have hc := (RamLang.Library.Fill.contract (free := free-5) rho mem l.scratch m (word w 0)
    hmfit).reprogram p (by repeat constructor)
  obtain ⟨flow,mem₁,log₁,clear,⟨hf,hmem,hp₁⟩,ht₁,hs₁⟩ := hc
  subst flow
  subst mem₁
  have hcinput : ArrayAt cleared l.input keys := by
    intro i
    have hi : i.val < N := by simpa [hlen] using i.isLt
    have hout := Region.not_contains_of_separated ha.separated (Region.contains_index ha.input hi)
    have hout' : ¬ (Region.mk l.scratch m).Contains (word w (l.input+i.val)) := by
      intro h
      apply hout
      change l.scratch ≤ (word w (l.input+i.val)).toNat ∧ (word w (l.input+i.val)).toNat < l.scratch+6*(N+1)
      simp only [Region.Contains] at h
      omega
    exact (RamLang.Logic.Fill.filled_outside mem l.scratch m (word w 0) _ hout').trans (hinput i)
  have hrep : Representation w N l m hash [] cleared :=
    Representation.empty (RamLang.Logic.Fill.filled_array mem l.scratch m (word w 0) hmfit)
  have hl := loop_contract (free := free) p rho cleared l hash seed shift [] keys
    ![some (word w 2*(word w N+word w 1)),some (word w N+word w 1),some (word w 2*word w N),
      some (word w 0),none,none,none,none,none,none,none,none,none,none,none]
    hsearch hfree ha hm hh hhash hrep (by simp [hlen]) hcinput (by rfl) (by simp [hlen])
  have hl' : Contract p rho free loop (initialLocals l N m seed shift) cleared
      (fun flow mem' log => (policy l N).AllowsTrace log ∧ Representation w N l m hash (collect keys []) mem' ∧
        ∃ saved, flow = .next (locals l N (l.input+N) 0 m (collect keys []).length seed shift saved))
      (225*N+55*comparisons hash keys []+5) 10 := by
    simpa [initialLocals,locals,Layout.nodes,Layout.compact,WordRam.word_mul,WordRam.word_add,hlen] using hl
  obtain ⟨flow,mem₂,log₂,body,⟨hp₂,hrep',saved,hflow⟩,ht₂,hs₂⟩ := hl'
  subst flow
  have hp₁' : (policy l N).AllowsTrace log₁ := by
    intro e he
    have h := hp₁ e he
    cases e with
    | dataRead => exact False.elim h
    | randomRead => exact False.elim h
    | dataWrite a v =>
      change l.scratch ≤ a.toNat ∧ a.toNat < l.scratch+6*(N+1)
      change l.scratch ≤ a.toNat ∧ a.toNat < l.scratch+m at h
      omega
  have hclearSpace : 5 ≤ free := by omega
  refine ⟨_,_,_,by ram_derive (dedup_test),?_,?_,?_⟩
  · simpa [AccessPolicy.allowsTrace_append] using And.intro hrep' (And.intro hp₁' hp₂)
  · ram_cost
    omega
  · ram_cost
    change 5+extraStack clear ≤ 10 ∧ extraStack body ≤ 10
    omega

end Dedup.Source.Pass
