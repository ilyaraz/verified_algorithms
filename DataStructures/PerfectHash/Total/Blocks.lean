import DataStructures.PerfectHash.Total.MachineCode

namespace PerfectHash.Total
open WordRam Construction.Registers Bounded.Registers
set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

open Bounded
macro "total_reduce" : tactic => `(tactic|
  simp [PerfectHash.Total.program_eq,
    run,step,Comparison.test,Operand.eval,State.put,update,RunResult.prepend,
    Construction.Registers.seed,Construction.Registers.status,
    trialsLeft,stage,fallbackMode, *])

def fallbackState (s : State w 64) (pc : Nat) (a : Word w) : State w 64 :=
  ⟨pc,update (update (update s.regs status (word w 0)) seed a) fallbackMode (word w 1),s.mem⟩

theorem root_first (s : State w 64) (rho : RandomMemory w)
    (hp : s.pc = 86) (hn : s.regs trialsLeft = word w 0)
    (hm : s.regs fallbackMode = word w 0) (hs : s.regs stage = word w 0) :
    Steps PerfectHash.Total.program rho 7 s (fallbackState s 93 (word w 1)) [] := by
  change s.regs (32 : Reg 64) = word w 0 at hn
  change s.regs (40 : Reg 64) = _ at hm
  change s.regs (34 : Reg 64) = _ at hs
  apply steps_iff_run.mpr
  unfold fallbackState
  total_reduce

theorem root_next (s : State w 64) (rho : RandomMemory w)
    (hp : s.pc = 86) (hn : s.regs trialsLeft = word w 0)
    (hm : s.regs fallbackMode = word w 1) (hs : s.regs stage = word w 0)
    (hone : word w 1 ≠ word w 0) :
    Steps PerfectHash.Total.program rho 7 s (fallbackState s 93 (s.regs seed+word w 2)) [] := by
  change s.regs (32 : Reg 64) = word w 0 at hn
  change s.regs (40 : Reg 64) = _ at hm
  change s.regs (34 : Reg 64) = _ at hs
  apply steps_iff_run.mpr
  unfold fallbackState
  total_reduce
  funext r
  simp [update]
  split <;> simp_all

theorem child_first (s : State w 64) (rho : RandomMemory w)
    (hp : s.pc = 179) (hn : s.regs trialsLeft = word w 0)
    (hm : s.regs fallbackMode = word w 0) (hs : s.regs stage = word w 1)
    (hone : word w 1 ≠ word w 0) :
    Steps PerfectHash.Total.program rho 8 s (fallbackState s 188 (word w 1)) [] := by
  change s.regs (32 : Reg 64) = word w 0 at hn
  change s.regs (40 : Reg 64) = _ at hm
  change s.regs (34 : Reg 64) = _ at hs
  apply steps_iff_run.mpr
  unfold fallbackState
  total_reduce

theorem child_next (s : State w 64) (rho : RandomMemory w)
    (hp : s.pc = 179) (hn : s.regs trialsLeft = word w 0)
    (hm : s.regs fallbackMode = word w 1) (hs : s.regs stage = word w 1)
    (hone : word w 1 ≠ word w 0) :
    Steps PerfectHash.Total.program rho 8 s (fallbackState s 188 (s.regs seed+word w 2)) [] := by
  change s.regs (32 : Reg 64) = word w 0 at hn
  change s.regs (40 : Reg 64) = _ at hm
  change s.regs (34 : Reg 64) = _ at hs
  apply steps_iff_run.mpr
  unfold fallbackState
  total_reduce
  funext r
  simp [update]
  split <;> simp_all

end PerfectHash.Total
