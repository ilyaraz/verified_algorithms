import DataStructures.PerfectHash.Construction.RootProgram

namespace PerfectHash.Construction.Root
open WordRam Registers

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

macro "root_reduce" : tactic => `(tactic|
  simp [program,assembly,location,Assembly.assemble,Assembly.instructions,
    Assembly.labelOffset,Assembly.Instruction.resolve,Instr.relocate,
    run,step,Comparison.test,Operand.eval,State.put,update,update_shadow,RunResult.prepend,
    Registers.input,count,directory,nodes,width,seed,shift,budget,remaining,distinct,key,
    Registers.hash,address,oldCount,oldHead,increment,node,temp,status,clearCursor,
    clearRemaining,buckets, *])

def initial (s : State w 64) : State w 64 :=
  ⟨5,update (update (update (update (update s.regs remaining (s.regs count))
    distinct (word w 0)) budget (s.regs count*word w 6))
    clearCursor (s.regs directory)) clearRemaining (s.regs buckets*word w 4),s.mem⟩

theorem entry (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 0) :
    Steps program rho 5 s (initial s) [] := by
  apply steps_iff_run.mpr
  unfold initial
  root_reduce

def hashed (s : State w 64) : Word w :=
  unsignedShiftRight (s.regs seed*s.mem (s.regs Registers.input)) (s.regs shift)

def bucketAddress (s : State w 64) : Addr w := s.regs directory+hashed s*word w 4

def probe (s : State w 64) : State w 64 :=
  ⟨19,update (update (update (update (update s.regs key (s.mem (s.regs Registers.input)))
    Registers.hash (hashed s)) address (bucketAddress s)) oldCount (s.mem (bucketAddress s)))
    increment (s.mem (bucketAddress s)*word w 2+word w 1),s.mem⟩

def probeTrace (s : State w 64) : List (Access w) :=
  [.dataRead (s.regs Registers.input) (s.mem (s.regs Registers.input)),
   .dataRead (bucketAddress s) (s.mem (bucketAddress s))]

theorem probe_next (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 10)
    (hn : s.regs remaining ≠ word w 0) :
    Steps program rho 9 s (probe s) (probeTrace s) := by
  change s.regs (8 : Reg 64) ≠ word w 0 at hn
  apply steps_iff_run.mpr
  unfold probe probeTrace bucketAddress hashed
  root_reduce

theorem reject (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 19)
    (h : (s.regs budget).toNat < (s.regs increment).toNat) :
    Steps program rho 1 s {s with pc := 37} [] := by
  change (s.regs (7 : Reg 64)).toNat < (s.regs (15 : Reg 64)).toNat at h
  apply steps_iff_run.mpr
  root_reduce

theorem accept (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 19)
    (h : (s.regs increment).toNat ≤ (s.regs budget).toNat) :
    Steps program rho 1 s {s with pc := 20} [] := by
  have hn : ¬ (s.regs (7 : Reg 64)).toNat < (s.regs (15 : Reg 64)).toNat := Nat.not_lt.mpr h
  apply steps_iff_run.mpr
  root_reduce

def newNode (s : State w 64) : Addr w := s.regs nodes+s.regs distinct*word w 2

def insertedMemory (s : State w 64) : DataMemory w :=
  update (update (update (update s.mem (newNode s) (s.regs key))
    (newNode s+word w 1) (s.mem (s.regs address+word w 1)))
    (s.regs address+word w 1) (s.regs distinct+word w 1))
    (s.regs address) (s.regs oldCount+word w 1)

def inserted (s : State w 64) : State w 64 :=
  ⟨10,update (update (update (update (update (update (update (update s.regs
    budget (s.regs budget-s.regs increment)) temp (s.regs address+word w 1))
    oldHead (s.mem (s.regs address+word w 1))) node (newNode s+word w 1))
    distinct (s.regs distinct+word w 1)) oldCount (s.regs oldCount+word w 1))
    Registers.input (s.regs Registers.input+word w 1)) remaining (s.regs remaining-word w 1),
    insertedMemory s⟩

def insertedTrace (s : State w 64) : List (Access w) :=
  [.dataRead (s.regs address+word w 1) (s.mem (s.regs address+word w 1)),
   .dataWrite (newNode s) (s.regs key),
   .dataWrite (newNode s+word w 1) (s.mem (s.regs address+word w 1)),
   .dataWrite (s.regs address+word w 1) (s.regs distinct+word w 1),
   .dataWrite (s.regs address) (s.regs oldCount+word w 1)]

theorem insert_next (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 20) :
    Steps program rho 15 s (inserted s) (insertedTrace s) := by
  apply steps_iff_run.mpr
  unfold inserted insertedMemory insertedTrace newNode
  root_reduce

theorem exhausted (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 10)
    (hn : s.regs remaining = word w 0) :
    TerminatesIn program rho s 3 ⟨36,update s.regs status (word w 1),s.mem⟩ [] := by
  change s.regs (8 : Reg 64) = word w 0 at hn
  apply terminatesIn_iff_run.mpr
  root_reduce

theorem rejected (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 37) :
    TerminatesIn program rho s 2 ⟨38,update s.regs status (word w 0),s.mem⟩ [] := by
  apply terminatesIn_iff_run.mpr
  root_reduce

end PerfectHash.Construction.Root
