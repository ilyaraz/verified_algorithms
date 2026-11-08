import DataStructures.PerfectHash.Construction.ChildProgram

namespace PerfectHash.Construction.Child
open WordRam Registers

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

macro "child_reduce" : tactic => `(tactic|
  simp [program,assembly,location,Assembly.assemble,Assembly.instructions,
    Assembly.labelOffset,Assembly.Instruction.resolve,Instr.relocate,
    run,step,Comparison.test,Operand.eval,State.put,update,update_shadow,RunResult.prepend,
    Registers.input,count,directory,nodes,width,seed,shift,budget,remaining,distinct,key,
    Registers.hash,address,oldCount,oldHead,increment,node,temp,status,clearCursor,
    clearRemaining,buckets,table,slots,cursor,slot,flag,rootHead, *])

def initial (s : State w 64) : State w 64 :=
  ⟨2,update (update s.regs clearCursor (s.regs table)) clearRemaining (s.regs slots*word w 2),s.mem⟩

theorem entry (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 0) :
    Steps program rho 2 s (initial s) [] := by
  apply steps_iff_run.mpr
  unfold initial
  child_reduce

def startLoop (s : State w 64) : State w 64 := ⟨8,update s.regs cursor (s.regs rootHead),s.mem⟩

theorem start_loop (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 7) :
    Steps program rho 1 s (startLoop s) [] := by
  apply steps_iff_run.mpr
  unfold startLoop
  child_reduce

def nodeAddress (s : State w 64) : Addr w := s.regs nodes+(s.regs cursor-word w 1)*word w 2

def hashed (s : State w 64) : Word w :=
  unsignedShiftRight (s.regs seed*s.mem (nodeAddress s)) (s.regs shift)

def slotAddress (s : State w 64) : Addr w := s.regs table+hashed s*word w 2

def probe (s : State w 64) : State w 64 :=
  ⟨18,update (update (update (update (update s.regs node (nodeAddress s))
    key (s.mem (nodeAddress s))) Registers.hash (hashed s)) slot (slotAddress s))
    flag (s.mem (slotAddress s)),s.mem⟩

def probeTrace (s : State w 64) : List (Access w) :=
  [.dataRead (nodeAddress s) (s.mem (nodeAddress s)),
   .dataRead (slotAddress s) (s.mem (slotAddress s))]

theorem probe_next (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 8)
    (hn : s.regs cursor ≠ word w 0) : Steps program rho 10 s (probe s) (probeTrace s) := by
  change s.regs (24 : Reg 64) ≠ word w 0 at hn
  apply steps_iff_run.mpr
  unfold probe probeTrace slotAddress hashed nodeAddress
  child_reduce

theorem accept (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 18)
    (hf : s.regs flag = word w 0) : Steps program rho 1 s {s with pc := 19} [] := by
  change s.regs (26 : Reg 64) = word w 0 at hf
  apply steps_iff_run.mpr
  child_reduce

theorem reject (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 18)
    (hf : s.regs flag ≠ word w 0) : Steps program rho 1 s {s with pc := 27} [] := by
  change s.regs (26 : Reg 64) ≠ word w 0 at hf
  apply steps_iff_run.mpr
  child_reduce

def insertedMemory (s : State w 64) : DataMemory w :=
  update (update s.mem (s.regs slot) (word w 1)) (s.regs slot+word w 1) (s.regs key)

def inserted (s : State w 64) : State w 64 :=
  ⟨8,update (update (update s.regs slot (s.regs slot+word w 1)) node (s.regs node+word w 1))
    cursor (insertedMemory s (s.regs node+word w 1)),insertedMemory s⟩

def insertedTrace (s : State w 64) : List (Access w) :=
  [.dataWrite (s.regs slot) (word w 1),.dataWrite (s.regs slot+word w 1) (s.regs key),
   .dataRead (s.regs node+word w 1) (insertedMemory s (s.regs node+word w 1))]

theorem insert_next (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 19) :
    Steps program rho 6 s (inserted s) (insertedTrace s) := by
  apply steps_iff_run.mpr
  unfold inserted insertedMemory insertedTrace
  child_reduce
  simp [insertedMemory,update,node,slot,key]

theorem exhausted (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 8)
    (hn : s.regs cursor = word w 0) :
    TerminatesIn program rho s 3 ⟨26,update s.regs status (word w 1),s.mem⟩ [] := by
  change s.regs (24 : Reg 64) = word w 0 at hn
  apply terminatesIn_iff_run.mpr
  child_reduce

theorem rejected (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 27) :
    TerminatesIn program rho s 2 ⟨28,update s.regs status (word w 0),s.mem⟩ [] := by
  apply terminatesIn_iff_run.mpr
  child_reduce

end PerfectHash.Construction.Child
