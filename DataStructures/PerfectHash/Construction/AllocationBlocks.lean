import DataStructures.PerfectHash.Construction.AllocationProgram

namespace PerfectHash.Construction.Allocation
open WordRam Registers

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

macro "allocation_reduce" : tactic => `(tactic|
  simp [program,assembly,location,Assembly.assemble,Assembly.instructions,
    Assembly.labelOffset,Assembly.Instruction.resolve,Instr.relocate,
    run,step,Comparison.test,Operand.eval,State.put,update,update_shadow,RunResult.prepend,
    address,temp,rootHead,width,childCount,slots,size,shift,roundTarget,table,tableEnd, *])

def loaded (s : State w 64) (pc : Nat) : State w 64 :=
  ⟨pc,update (update (update (update (update s.regs childCount (s.mem (s.regs address)))
    temp (s.regs address+word w 1)) rootHead (s.mem (s.regs address+word w 1)))
    shift (s.regs width)) slots (s.mem (s.regs address)),s.mem⟩

def loadTrace (s : State w 64) : List (Access w) :=
  [.dataRead (s.regs address) (s.mem (s.regs address)),
   .dataRead (s.regs address+word w 1) (s.mem (s.regs address+word w 1))]

theorem direct (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 0)
    (hb : (s.mem (s.regs address)).toNat ≤ (word w 1).toNat) :
    Steps program rho 6 s (loaded s 14) (loadTrace s) := by
  change (s.mem (s.regs (12 : Reg 64))).toNat ≤ (word w 1).toNat at hb
  simp only [word_toNat] at hb
  apply steps_iff_run.mpr
  unfold loaded loadTrace
  allocation_reduce

def initialized (s : State w 64) : State w 64 :=
  ⟨9,update (update (loaded s 6).regs roundTarget
    (s.mem (s.regs address)*s.mem (s.regs address)*word w 2)) size (word w 1),s.mem⟩

theorem hashed (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 0)
    (hb : (word w 1).toNat < (s.mem (s.regs address)).toNat) :
    Steps program rho 9 s (initialized s) (loadTrace s) := by
  change (word w 1).toNat < (s.mem (s.regs (12 : Reg 64))).toNat at hb
  simp only [word_toNat] at hb
  have hn := Nat.not_le.mpr hb
  apply steps_iff_run.mpr
  unfold initialized loaded loadTrace
  allocation_reduce

def rounded (s : State w 64) : State w 64 := ⟨14,update s.regs slots (s.regs size),s.mem⟩

theorem rounded_next (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 13) :
    Steps program rho 1 s (rounded s) [] := by
  apply steps_iff_run.mpr
  unfold rounded
  allocation_reduce

def finalMemory (s : State w 64) : DataMemory w :=
  update (update s.mem (s.regs address+word w 3) (s.regs table))
    (s.regs address+word w 2) (s.regs shift)

def finished (s : State w 64) : State w 64 :=
  ⟨20,update (update s.regs tableEnd (s.regs table+s.regs slots*word w 2))
    temp (s.regs address+word w 2),finalMemory s⟩

def finishTrace (s : State w 64) : List (Access w) :=
  [.dataWrite (s.regs address+word w 3) (s.regs table),
   .dataWrite (s.regs address+word w 2) (s.regs shift)]

theorem finish_next (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 14) :
    TerminatesIn program rho s 7 (finished s) (finishTrace s) := by
  apply terminatesIn_iff_run.mpr
  unfold finished finalMemory finishTrace
  allocation_reduce
  funext r
  simp [update]
  split <;> simp_all [update]

end PerfectHash.Construction.Allocation
