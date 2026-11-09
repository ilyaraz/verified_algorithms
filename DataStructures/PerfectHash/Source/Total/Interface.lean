import DataStructures.PerfectHash.Source.Total.Fuel
import DataStructures.PerfectHash.Source.Query.Correctness

namespace PerfectHash.Source.Total
open WordRam RamLang RamLang.Compiler PerfectHash.Bounded

/-- A successful run's released construction stack is a valid query stack.
Only the retained output must survive; dirty input and scratch need no reset. -/
theorem query_stack {w : Nat} {xs : List (Word w)} {l : Layout} {t : State w StaticSet.registerCount}
    (ha : Admissible w xs.length l) (hb : Public.Built xs l t) :
    Query.Admissible w (StaticSet.readDescriptor t.regs) (Entry.stack l xs.length) := by
  obtain ⟨_,hbase,hsize,_,_⟩ := hb.descriptor
  refine ⟨by have h := ha.codeFit; omega,Entry.stack_fits ha.toAdmissible,?_,?_⟩
  · change 28 ≤ 58*(xs.length+1)
    omega
  · have hd := List.toFinset_card_le xs
    have hs := ha.ordinary.output_scratch
    simp only [Region.Separated,Layout.output,Layout.scratch,dictionaryCapacity,workspaceCapacity] at hs
    simp only [Region.Separated,Entry.stack,hbase]
    omega

/-- Successful fixed-fuel construction exposes a valid retained dictionary. -/
theorem successful_representation {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w StaticSet.registerCount}
    (ha : Admissible w xs.length l) (rho : RandomMemory w) (hpc : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (hinput : ArrayAt s.mem l.inputBase xs) :
    Public.Built xs l (WordRam.run program rho (fuel w xs.length) s).state := by
  obtain ⟨k,t,trace,he,_,_,hp,_,_⟩ := run_total ha rho hpc hin hinput
  rw [he]
  exact hp

/-- Query after construction permits arbitrary overwriting outside the returned
extent and reuses construction scratch as its stack. Every word query has the
proved constant 237-instruction bound and exact set membership. -/
theorem query_after_build {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w StaticSet.registerCount}
    (ha : Admissible w xs.length l) (rho : RandomMemory w) (hpc : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (hinput : ArrayAt s.mem l.inputBase xs)
    (queryState : State w ABI.registers) (key : Word w) (queryRandom : RandomMemory w)
    (agree : AgreeOn (StaticSet.readDescriptor (WordRam.run program rho (fuel w xs.length) s).state.regs)
      (WordRam.run program rho (fuel w xs.length) s).state.mem queryState.mem)
    (hi : Query.Input (StaticSet.readDescriptor (WordRam.run program rho (fuel w xs.length) s).state.regs)
      (Entry.stack l xs.length) key queryState) :
    Query.Output xs.toFinset (StaticSet.readDescriptor (WordRam.run program rho (fuel w xs.length) s).state.regs)
      (Entry.stack l xs.length) key queryState.mem (WordRam.run Query.compiled.code queryRandom Query.cost queryState) := by
  have hb := successful_representation ha rho hpc hin hinput
  obtain ⟨table,hview⟩ := hb.descriptor.1
  exact Query.after_overwrite queryRandom queryState key hview agree (query_stack ha hb) hi

/-- Fresh source scheduling survives compilation: random addresses are unique
and bounded by the reservation based on the distinct count. -/
theorem random_reads {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w StaticSet.registerCount}
    (ha : Admissible w xs.length l) (rho : RandomMemory w) (hpc : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (hinput : ArrayAt s.mem l.inputBase xs) :
    (WordRam.run program rho (fuel w xs.length) s).randomAddresses.Nodup ∧
      (WordRam.run program rho (fuel w xs.length) s).randomReads ≤ randomCapacity w (StaticSet.distinctCount xs) := by
  obtain ⟨k,t,trace,he,_,_,_,_,hr⟩ := run_total ha rho hpc hin hinput
  rw [he]
  constructor
  · exact (consecutiveAddresses_nodup (random_span_fit ha.toAdmissible)).sublist hr
  · have hh := hr.length_le
    simp only [consecutiveAddresses_length] at hh
    exact hh.trans (random_span_le xs)

end PerfectHash.Source.Total
