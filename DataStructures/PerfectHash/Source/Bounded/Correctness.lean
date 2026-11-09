import RamLang.Compiler.Metadata
import DataStructures.PerfectHash.Source.Public
import DataStructures.PerfectHash.Source.Bounded.RootSearch
import DataStructures.PerfectHash.Source.Bounded.ChildSearch

namespace PerfectHash.Source.Bounded
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Bounded
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- The final public constructor is one fixed program generated from the DSL. -/
def program : WordRam.Program StaticSet.registerCount := Public.program compiled

/-- The shared function bodies and standard dummy entry occupy 1,677 instructions. -/
theorem compiled_size : compiled.code.size = 1677 := by
  rw [compile_code_size compiles]
  rfl

/-- The final adapter and compiled functions occupy 1,720 instructions. -/
theorem program_size : program.size = 1720 := by
  rw [program,Public.program_size,compiled_size]

/-- The additional code-address condition is explicit; all original layout,
linear arithmetic and random reservations stay the same. -/
structure Admissible (w N : Nat) (l : Layout) extends PerfectHash.Admissible w N l : Prop where
  codeFit : 1720 < modulus w

/-- All ordinary callee frames fit whenever the complete generated code fits. -/
theorem fits (hw : 1720 < modulus w) : compiled.Fits w := by
  have hf : ∀ layout ∈ compiled.functions, layout.frameWords ≤ 30 := by
    rw [compile_layouts compiles]
    decide
  refine ⟨?_,?_⟩
  · rw [compiled_size]
    omega
  · intro layout hl
    have hh := hf layout hl
    omega

/-- Explicit old sufficient widths also satisfy the new code-address condition. -/
theorem canonical_admissible (hw : 256*(N+1) ≤ w) : Admissible w N (canonicalLayout N) := by
  refine ⟨canonical_admissible_of_large_width hw,?_⟩
  have hh := Nat.pow_le_pow_right (n := 2) (by decide) (show 11 ≤ w by omega)
  change 1720 < 2^w
  omega

/-- The actual stopped-work majorant includes the public entry and final halt. -/
def constructionWork (xs : List (Word w)) (l : Layout) (ha : PerfectHash.Admissible w xs.length l)
    (rho : RandomMemory w) : Nat :=
  Constructor.work xs l ha rho (rootChoice xs l rho) (rootWork xs l rho) (fun a => searchWork xs l a rho)+40

/-- Every bounded source program invocation terminates normally with success
or an exhausted search block. Stack exhaustion is impossible under admissibility. -/
theorem execution {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w StaticSet.registerCount}
    (ha : Admissible w xs.length l) (rho : RandomMemory w) (hpc : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (hinput : ArrayAt s.mem l.inputBase xs) :
    ∃ k t trace, WordRam.TerminatesIn program rho s k t trace ∧ k ≤ constructionWork xs l ha.toAdmissible rho ∧
      t.regs ⟨5,by decide⟩ = word w 1 ∧
      ((t.regs ⟨18,by decide⟩ = word w 0 ∧
        Constructor.Failed (rootChoice xs l rho) (fun a b => childChoice xs l a b rho)) ∨ Public.Built xs l t) ∧
      (PerfectHash.Bounded.policy w xs.length l).AllowsTrace trace ∧
      (trace.filterMap Access.randomAddress).Sublist (consecutiveAddresses w l.randomBase (randomSpan w xs)) := by
  have hc := Constructor.contract (free := (Entry.stack l xs.length).size-30) source rho s.mem xs l ha.toAdmissible
    Source.Search.Root.function Source.Search.Child.function (rootChoice xs l rho) (rootWork xs l rho)
    (fun a b => childChoice xs l a b rho) (fun a => searchWork xs l a rho)
    (root_search_spec source rho xs l ha.toAdmissible rfl rfl rfl rfl)
    (fun a hy => child_search_spec source rho xs l a ha.toAdmissible hy rfl rfl rfl rfl)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl (by have h := Constructor.stack_sufficient l xs.length; omega) hinput
  exact Public.execution ha.toAdmissible hpc hin compiles (fits ha.codeFit)
    (by rw [Machine.code_size,compiled_size]; exact ha.codeFit) rfl hc

/-- Interrupted executions obey the same full memory policy, including every
partially initialized call frame, and no instruction prefix can fault. -/
theorem prefix_safety {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w StaticSet.registerCount}
    (ha : Admissible w xs.length l) (rho : RandomMemory w) (hpc : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (hinput : ArrayAt s.mem l.inputBase xs) (fuel : Nat) :
    (PerfectHash.Bounded.policy w xs.length l).AllowsTrace (WordRam.run program rho fuel s).trace ∧
      ∀ fault, (WordRam.run program rho fuel s).reason ≠ .fault fault := by
  obtain ⟨k,t,trace,ht,_,_,_,hp,_⟩ := execution ha rho hpc hin hinput
  exact ⟨ht.prefix_policy hp fuel,ht.noFault fuel⟩

/-- Compiler frames occupy the original scratch reservation, so peak ordinary
storage includes input, output, scratch and sixty-four registers exactly once. -/
theorem peak_memory (N : Nat) : peakWords N = N+128*(N+1)+64 ∧ peakWords N ≤ 193*(N+1) := by
  constructor
  · simp only [peakWords,dictionaryCapacity,workspaceCapacity,StaticSet.registerCount]
    omega
  · exact peakWords_le N

end PerfectHash.Source.Bounded
