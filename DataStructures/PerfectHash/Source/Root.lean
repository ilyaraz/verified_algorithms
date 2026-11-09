import RamLang.DSL.Derive
import RamLang.Library.Fill
import RamLang.Logic.Reprogram
import DataStructures.PerfectHash.Construction.Grouping

namespace PerfectHash.Source.Root
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Construction Buckets
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- One complete root trial clears dirty directory words and groups the input.
The linear energy increment is checked before subtraction and before any node
is inserted. The fill is an ordinary call, including its stack and time costs. -/
def program : RamLang.Program := ram_program main {
  fn main(configuration, seed, shift) {
    let input = load(configuration);
    let count = load(configuration + 1);
    let directory = load(configuration + 2);
    let nodes = load(configuration + 3);
    let buckets = load(configuration + 4);
    return root(input, count, directory, nodes, buckets, seed, shift);
  }
  fn root(input, count, directory, nodes, buckets, seed, shift) {
    let distinct = 0;
    let budget = 6 * count;
    fill(directory, 4 * buckets, 0);
    while (count != 0) {
      let key = load(input);
      let bucket = (seed * key) >> shift;
      let entry = directory + 4 * bucket;
      let oldCount = load(entry);
      let increment = 2 * oldCount + 1;
      if (budget < increment) { return 0; }
      budget = budget - increment;
      let head = load(entry + 1);
      let node = nodes + 2 * distinct;
      store(node, key);
      store(node + 1, head);
      store(entry + 1, distinct + 1);
      store(entry, oldCount + 1);
      distinct = distinct + 1;
      input = input + 1;
      count = count - 1;
    }
    return 1;
  }
  fn fill(p, n, value) {
    while (n != 0) { store(p, value); p = p + 1; n = n - 1; }
    return 0;
  }
}

/-- Callable root trial; the public component driver reads a five-word
configuration and passes its fields through ordinary function arguments. -/
def function : RamLang.Function := program.functions[1]'(by decide)

/-- The shared clearing helper has the previously proved source implementation. -/
theorem fill_eq : program.functions[2]? = some RamLang.Logic.Fill.function := rfl

/-- The loop is selected from the checked DSL term; this projection neither
executes code nor introduces a second implementation. -/
def loop : Stmt := match function.body with
  | .seq _ (.seq _ (.seq _ (.seq _ (.seq body _)))) => body
  | _ => .skip

/-- The finite syntax of one grouping iteration. -/
def iteration : Stmt := match loop with | .while _ body => body | _ => .skip

/-- Scratch locals have fixed size and arbitrary contents at loop boundaries. -/
abbrev Scratch (w : Nat) := Fin 18 → Option (Word w)

/-- Stable loop values followed by the compiler's eighteen scratch slots. -/
def locals (input remaining dir nodes m distinct budget : Nat) (seed shift : Word w)
    (old : Scratch w) : Locals w :=
  [some (word w input),some (word w remaining),some (word w dir),some (word w nodes),
   some (word w m),some seed,some shift,some (word w distinct),some (word w budget),
   old 0, old 1, old 2, old 3, old 4, old 5, old 6, old 7, old 8, old 9, old 10, old 11, old 12, old 13, old 14, old 15, old 16, old 17]

/-- Root grouping reads the input and directory and writes only the directory
and new nodes. Random memory is not accessed by a trial. -/
def policy (input : Region) (dir nodes m N : Nat) : AccessPolicy w :=
  ⟨fun a => input.Contains a ∨ (Region.mk dir (4*m)).Contains a,
   fun a => (Region.mk dir (4*m)).Contains a ∨ (Region.mk nodes (2*N)).Contains a,
   fun _ => False⟩

macro "root_test" : tactic => `(tactic|
  simp [Condition.eval,Atom.eval,requireSome,Comparison.test,Binary.eval,
    bind,pure,Except.bind,Except.pure,WordRam.word_add,WordRam.word_mul, *] <;> omega)

/-- A grouping iteration either rejects without writing or implements exactly
the existing four-store grouping model. Its increment is a fitting linear
quantity even if the full energy would not fit in a word. -/
theorem iteration_contract {w free input remaining dir nodes m N budget : Nat}
    (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (hash : Word w → Fin m) (seed shift key : Word w) (seen : List (Word w))
    (old : Scratch w) (inputRegion : Region)
    (hspace : GroupSpace w m N dir nodes) (hn : seen.length < N)
    (hlinear : 64*(N+1) < modulus w) (hb : budget ≤ 6*N)
    (hr : 0 < remaining) (hkey : mem (word w input) = key)
    (hhash : unsignedShiftRight (seed*key) shift = word w (hash key).val)
    (hrep : Grouped hash dir nodes seen mem) (hread : inputRegion.Contains (word w input)) :
    Contract p rho free iteration (locals input remaining dir nodes m seen.length budget seed shift old) mem
      (fun flow mem' log => (policy inputRegion dir nodes m N).AllowsTrace log ∧
        if 2*count hash seen (hash key)+1 ≤ budget then
          mem' = groupMemory dir nodes seen.length (hash key).val (count hash seen (hash key)) key
            (word w (Dedup.firstIndex (Dedup.chain (fun x => (hash x).val) seen (hash key).val))) mem ∧
          ∃ saved, flow = .next (locals (input+1) (remaining-1) dir nodes m (seen.length+1)
            (budget-(2*count hash seen (hash key)+1)) seed shift saved)
        else flow = .returned (word w 0) ∧ mem' = mem) 220 0 := by
  have hc := hrep.counts (hash key)
  have hh := hrep.heads (hash key)
  have hi := energy_increment_fit hash seen key hn hlinear
  have hbudget := energy_budget_fit hb hlinear
  have hcmod := Nat.mod_eq_of_lt hi
  have hbmod := Nat.mod_eq_of_lt hbudget
  have hone : 1 < modulus w := by omega
  have hsub : word w remaining-word w 1 = word w (remaining-1) := WordRam.word_sub _ _ hone hr
  have hc₀ := Region.contains_index hspace.directory (by have := (hash key).isLt; omega : 4*(hash key).val < 4*m)
  have hc₁ := Region.contains_index hspace.directory (by have := (hash key).isLt; omega : 4*(hash key).val+1 < 4*m)
  have hn₀ := Region.contains_index hspace.nodes_fit (by omega : 2*seen.length < 2*N)
  have hn₁ := Region.contains_index hspace.nodes_fit (by omega : 2*seen.length+1 < 2*N)
  simp only [← Nat.add_assoc] at hc₁ hn₁
  by_cases he : 2*count hash seen (hash key)+1 ≤ budget
  · have hbudgetSub := WordRam.word_sub budget (2*count hash seen (hash key)+1) hi he
    refine ⟨_,_,_,by ram_derive (root_test),?_,?_,?_⟩
    · simp only [Binary.eval,hkey,hhash,WordRam.word_mul,WordRam.word_add,hc,hh,hsub,hbudgetSub,
        he,↓reduceIte]
      constructor
      · simp [policy,AccessPolicy.AllowsTrace,AccessPolicy.Allows,hread,hc₀,hc₁,hn₀,hn₁,← Nat.add_assoc]
      · constructor
        · simp [groupMemory,Nat.add_assoc]
        · refine ⟨![_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_],rfl⟩
    · ram_cost
    · ram_cost
  · refine ⟨_,_,_,by ram_derive (root_test),?_,?_,?_⟩
    · simp [Binary.eval,hkey,hhash,WordRam.word_mul,WordRam.word_add,hc,he,
        policy,AccessPolicy.AllowsTrace,AccessPolicy.Allows,hread,hc₀]
    · ram_cost
    · ram_cost

/-- A successful loop groups every remaining key; a rejected loop returns zero.
The cursor and count track the consumed array, while the remaining energy is a
runtime word and the processed lists exist only in this proof predicate. -/
def Post (hash : Word w → Fin m) (input dir nodes m budget : Nat) (seed shift : Word w)
    (seen rest : List (Word w)) (flow : Flow w) (mem : DataMemory w) : Prop :=
  if groupAccepted hash budget seen rest then
    ∃ remainingBudget saved, flow = .next (locals (input+rest.length) 0 dir nodes m
      (seen.length+rest.length) remainingBudget seed shift saved) ∧
      Grouped hash dir nodes (rest.reverse++seen) mem
  else flow = .returned (word w 0)

/-- The concrete grouping loop implements groupAccepted, with linear charged
instruction work, no nested frames, and all effects confined to its two output
regions. In particular the input survives every successful or rejected prefix. -/
theorem loop_contract {w free input dir nodes m N budget : Nat}
    (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (hash : Word w → Fin m) (seed shift : Word w) (seen rest : List (Word w))
    (old : Scratch w) (inputRegion : Region)
    (hspace : GroupSpace w m N dir nodes) (hn : seen.length+rest.length ≤ N)
    (hlinear : 64*(N+1) < modulus w) (hb : budget ≤ 6*N)
    (hinput : ArrayAt mem input rest)
    (hhash : ∀ key, unsignedShiftRight (seed*key) shift = word w (hash key).val)
    (hrep : Grouped hash dir nodes seen mem)
    (hfit : inputRegion.Fits w) (hstart : inputRegion.base ≤ input)
    (hend : input+rest.length ≤ inputRegion.base+inputRegion.size)
    (hdir : inputRegion.Separated ⟨dir,4*m⟩) (hnodes : inputRegion.Separated ⟨nodes,2*N⟩) :
    Contract p rho free loop (locals input rest.length dir nodes m seen.length budget seed shift old) mem
      (fun flow mem' log => (policy inputRegion dir nodes m N).AllowsTrace log ∧
        Post hash input dir nodes m budget seed shift seen rest flow mem') (225*rest.length+5) 0 := by
  induction rest generalizing input seen budget mem old with
  | nil =>
    exact Contract.ofEvaluation (.whileFalse (by rfl))
      ⟨by simp [AccessPolicy.AllowsTrace],by simpa [Post,groupAccepted] using
        (show ∃ b s, Flow.next (locals input 0 dir nodes m seen.length budget seed shift old) =
          .next (locals input 0 dir nodes m seen.length b seed shift s) ∧ Grouped hash dir nodes seen mem from
          ⟨budget,old,rfl,hrep⟩)⟩ (Nat.le_refl _) (Nat.le_refl _)
  | cons key rest ih =>
    have hlen : seen.length < N := by simp only [List.length_cons] at hn; omega
    have hcount : rest.length+1 < modulus w := by simp only [List.length_cons] at hn; omega
    have hzero : word w (rest.length+1) ≠ word w 0 := by
      intro he
      have := (word_eq_iff_of_lt hcount (by omega : 0 < modulus w)).mp he
      omega
    have htest : (Condition.mk .ne (.local 1) (.literal 0)).eval
        (locals input (key::rest).length dir nodes m seen.length budget seed shift old) = .ok true := by
      simp [Condition.eval,Atom.eval,requireSome,Comparison.test,locals,hzero,
        bind,pure,Except.bind,Except.pure]
    have hr : inputRegion.Contains (word w input) := by
      have hf : inputRegion.base+inputRegion.size < modulus w := hfit
      simp only [List.length_cons] at hend
      simp only [Region.Contains,word_toNat_of_lt (by omega : input < modulus w)]
      omega
    obtain ⟨hkey,htail⟩ := arrayAt_cons.mp hinput
    obtain ⟨flow,mem',log,d,⟨hp,hpost⟩,ht,hs⟩ :=
      iteration_contract (free := free) (remaining := rest.length+1) p rho mem hash seed shift key seen old inputRegion hspace hlen hlinear hb
        (by simp) hkey (hhash key) hrep hr
    by_cases he : 2*count hash seen (hash key)+1 ≤ budget
    · rw [if_pos he] at hpost
      obtain ⟨hmem,saved,hflow⟩ := hpost
      have hinput' : ArrayAt mem' (input+1) rest := by
        intro i
        rw [d.frame_of_policy hp]
        · exact htail i
        · intro ha
          have hh : inputRegion.Contains (word w (input+1+i.val)) := by
            have hf : inputRegion.base+inputRegion.size < modulus w := hfit
            have hi := i.isLt
            simp only [List.length_cons] at hend
            change inputRegion.base ≤ (word w (input+1+i.val)).toNat ∧
              (word w (input+1+i.val)).toNat < inputRegion.base+inputRegion.size
            rw [word_toNat_of_lt (by omega : input+1+i.val < modulus w)]
            omega
          rcases ha with ha | ha
          · exact (Region.not_contains_of_separated hdir hh) ha
          · exact (Region.not_contains_of_separated hnodes hh) ha
      have hrep' : Grouped hash dir nodes (key::seen) mem' := by
        rw [hmem]
        exact hrep.insert hspace hlen
      have hflow' : flow = .next (locals (input+1) rest.length dir nodes m (key::seen).length
          (budget-(2*count hash seen (hash key)+1)) seed shift saved) := by simpa using hflow
      subst flow
      obtain ⟨flow,mem'',suffix,tail,⟨hp',hq'⟩,ht',hs'⟩ :=
        ih (input := input+1) (budget := budget-(2*count hash seen (hash key)+1)) mem' (key::seen) saved (by simp only [List.length_cons] at *; omega)
          (by omega) hinput' hrep' (by omega) (by simp only [List.length_cons] at hend; omega)
      refine Contract.ofEvaluation (.whileContinue htest d tail)
        ⟨(AccessPolicy.allowsTrace_append _).mpr ⟨hp,hp'⟩,?_⟩ ?_ ?_
      · simp only [Post,groupAccepted,if_pos he] at ⊢
        simpa [Post,List.reverse_cons,List.append_assoc,
          Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq'
      · change 5+instructions d+instructions tail ≤ 225*(rest.length+1)+5
        omega
      · exact Nat.max_le.mpr ⟨hs,hs'⟩
    · rw [if_neg he] at hpost
      obtain ⟨hflow,_⟩ := hpost
      subst flow
      refine Contract.ofEvaluation (.whileStop htest d (by trivial))
        ⟨hp,by simp [Post,groupAccepted,he]⟩ ?_ (by simpa only [extraStack] using hs)
      change 4+instructions d ≤ 225*(rest.length+1)+5
      omega

/-- Loop entry locals immediately after the charged directory-clear call. The
raw products match the emitted source operations before arithmetic rewriting. -/
def initialLocals (input N dir nodes m : Nat) (seed shift : Word w) : Locals w :=
  [some (word w input),some (word w N),some (word w dir),some (word w nodes),some (word w m),
   some seed,some shift,some (word w 0),some (word w 6*word w N),some (word w 0),some (word w 4*word w m)] ++
   List.replicate 16 none

/-- A root trial on dirty memory returns exactly the existing capped-energy
acceptance predicate. Success establishes all bucket counts, heads, and linked
chains. Every call, clear, probe, branch and store is included in the bound. -/
theorem contract {w free input dir nodes m N : Nat} (p : RamLang.Program)
    (rho : RandomMemory w) (mem : DataMemory w) (hash : Word w → Fin m)
    (seed shift : Word w) (keys : List (Word w))
    (hlookup : p.functions[2]? = some RamLang.Logic.Fill.function) (hfree : 5 ≤ free)
    (hspace : GroupSpace w m N dir nodes) (hlen : keys.length = N)
    (hlinear : 64*(N+1) < modulus w) (hinput : ArrayAt mem input keys)
    (hhash : ∀ key, unsignedShiftRight (seed*key) shift = word w (hash key).val)
    (hfit : (Region.mk input N).Fits w)
    (hdir : (Region.mk input N).Separated ⟨dir,4*m⟩)
    (hnodes : (Region.mk input N).Separated ⟨nodes,2*N⟩) :
    Contract p rho free function.body
      ([word w input,word w N,word w dir,word w nodes,word w m,seed,shift].map some ++
        List.replicate function.locals.length none) mem
      (fun flow mem' log => flow = .returned (word w (if groupAccepted hash (6*N) [] keys then 1 else 0)) ∧
        (groupAccepted hash (6*N) [] keys = true → Grouped hash dir nodes keys.reverse mem') ∧
        (policy ⟨input,N⟩ dir nodes m N).AllowsTrace log) (300*(N+m+1)) 5 := by
  let cleared := RamLang.Logic.Fill.filled mem dir (4*m) (word w 0)
  have hc := (RamLang.Library.Fill.contract (free := free-5) rho mem dir (4*m) (word w 0)
    hspace.directory).reprogram p (by repeat constructor)
  have hc' : Contract p rho (free-5) RamLang.Logic.Fill.function.body
      [some (word w dir),some (word w 4*word w m),some (word w 0)] mem
      (fun flow mem' log => flow = .returned (word w 0) ∧ mem' = cleared ∧
        (RamLang.Logic.Fill.policy dir (4*m)).AllowsTrace log) (22*(4*m)+12) 0 := by
    simpa only [WordRam.word_mul] using hc
  obtain ⟨flow,mem₁,log₁,clear,⟨hf,hm,hp₁⟩,ht₁,hs₁⟩ := hc'
  subst flow
  subst mem₁
  have ha : ArrayAt cleared input keys := by
    intro i
    have hi : i.val < N := by simpa [hlen] using i.isLt
    exact (RamLang.Logic.Fill.filled_outside mem dir (4*m) (word w 0) _
      (Region.not_contains_of_separated hdir (Region.contains_index hfit hi))).trans (hinput i)
  have hg : Grouped hash dir nodes [] cleared :=
    Grouped.empty (RamLang.Logic.Fill.filled_array mem dir (4*m) (word w 0) hspace.directory)
  have hl := loop_contract (free := free) (budget := 6*N) p rho cleared hash seed shift [] keys
    ![some (word w 0),some (word w 4*word w m),none,none,none,none,none,none,none,none,
      none,none,none,none,none,none,none,none] ⟨input,N⟩ hspace (by simp [hlen]) hlinear (by omega)
      ha hhash hg hfit (by rfl) (by simp [hlen]) hdir hnodes
  have hl' : Contract p rho free loop (initialLocals input N dir nodes m seed shift) cleared
      (fun flow mem' log => (policy ⟨input,N⟩ dir nodes m N).AllowsTrace log ∧
        Post hash input dir nodes m (6*N) seed shift [] keys flow mem') (225*N+5) 0 := by
    simpa [initialLocals,locals,hlen,WordRam.word_mul] using hl
  obtain ⟨flow,mem₂,log₂,body,⟨hp₂,hq⟩,ht₂,hs₂⟩ := hl'
  have hp₁' : (policy ⟨input,N⟩ dir nodes m N).AllowsTrace log₁ := by
    intro e he
    have hh := hp₁ e he
    cases e with
    | dataRead => exact False.elim hh
    | randomRead => exact False.elim hh
    | dataWrite => exact Or.inl hh
  cases he : groupAccepted hash (6*N) [] keys with
  | false =>
    simp only [Post,he,Bool.false_eq_true,↓reduceIte] at hq
    subst flow
    refine ⟨_,_,_,by ram_derive (root_test),?_,?_,?_⟩
    · simpa [he,AccessPolicy.allowsTrace_append] using And.intro hp₁' hp₂
    · ram_cost
      omega
    · ram_cost
      change 5+extraStack clear ≤ 5 ∧ extraStack body ≤ 5
      omega
  | true =>
    simp only [Post,he,↓reduceIte,List.nil_append,List.append_nil,List.length_nil,Nat.zero_add] at hq
    obtain ⟨budget,saved,hflow,hgroup⟩ := hq
    subst flow
    refine ⟨_,_,_,by ram_derive (root_test),?_,?_,?_⟩
    · simpa [he,AccessPolicy.allowsTrace_append] using And.intro hgroup (And.intro hp₁' hp₂)
    · ram_cost
      omega
    · ram_cost
      change 5+extraStack clear ≤ 5 ∧ extraStack body ≤ 5
      omega

end PerfectHash.Source.Root
