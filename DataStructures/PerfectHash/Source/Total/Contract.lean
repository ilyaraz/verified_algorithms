import DataStructures.PerfectHash.Source.Total.Interface
import DataStructures.PerfectHash.Source.Total.Expected

namespace PerfectHash.Source.Total
open WordRam RamLang

/-- Public output of the alternative successful constructor. The retained
representation is unchanged; the query uses the ordinary language stack ABI. -/
structure Output (xs : List (Word w)) (l : Layout) (initial : DataMemory w)
    (result : RunResult w StaticSet.registerCount) : Prop where
  halted : result.reason = .halted
  runtime : result.state.regs ⟨5,by decide⟩ = word w 1
  built : Public.Built xs l result.state
  accesses : (PerfectHash.Bounded.policy w xs.length l).AllowsTrace result.trace
  fresh : result.randomAddresses.Nodup
  randomBound : result.randomReads ≤ randomCapacity w (StaticSet.distinctCount xs)
  frame : ∀ a, ¬ (l.output xs.length).Contains a → ¬ (l.scratch xs.length).Contains a →
    result.state.mem a = initial a

/-- Total source construction satisfies the public output contract for every image. -/
theorem construction_correct {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w StaticSet.registerCount}
    (ha : Admissible w xs.length l) (rho : RandomMemory w) (hpc : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (hinput : ArrayAt s.mem l.inputBase xs) :
    Output xs l s.mem (run program rho (fuel w xs.length) s) := by
  obtain ⟨k,t,trace,he,_,hstatus,hb,hp,_⟩ := run_total ha rho hpc hin hinput
  have hr := random_reads ha rho hpc hin hinput
  refine ⟨by rw [he],by simpa [he] using hstatus,by simpa [he] using hb,
    by simpa [he] using hp,hr.1,hr.2,?_⟩
  exact frame ha rho hpc hin hinput (fuel w xs.length)

/-- Complete alternative dictionary specification with explicit code fit and
ordinary-stack query effects. The original strict-read-only contract is intact. -/
structure Spec : Prop where
  construction : ∀ (w : Nat) (xs : List (Word w)) (l : Layout) (s : State w StaticSet.registerCount),
    Admissible w xs.length l → s.pc = 0 → BuildInput w xs.length l s.regs → ArrayAt s.mem l.inputBase xs →
      ∀ rho, Output xs l s.mem (run program rho (fuel w xs.length) s)
  expected : ∀ (w : Nat) (xs : List (Word w)) (l : Layout) (s : State w StaticSet.registerCount),
    Admissible w xs.length l → s.pc = 0 → BuildInput w xs.length l s.regs → ArrayAt s.mem l.inputBase xs →
      expectedSteps program (fuel w xs.length) s ≤ (10000000*(xs.length+1) : Nat)
  retained : ∀ (w : Nat) (xs : List (Word w)) (l : Layout) (t : State w StaticSet.registerCount),
    Public.Built xs l t → (StaticSet.readDescriptor t.regs).size ≤ 64*(xs.toFinset.card+1)
  peak : ∀ N, peakWords N ≤ 193*(N+1)
  query : Query.Spec

/-- The DSL constructor and query meet the complete alternative public specification. -/
theorem specification : Spec := by
  refine ⟨?_,?_,?_,peakWords_le,Query.spec⟩
  · intro w xs l s ha hpc hin hinput rho
    exact construction_correct ha rho hpc hin hinput
  · intro w xs l s ha hpc hin hinput
    exact expected_instructions ha hpc hin hinput
  · intro w xs l t hb
    exact hb.descriptor.2.2.1

end PerfectHash.Source.Total
