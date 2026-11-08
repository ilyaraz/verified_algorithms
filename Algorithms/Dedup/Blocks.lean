import Algorithms.Dedup.Program
import Algorithms.Dedup.Representation

namespace Dedup.Blocks
open WordRam Registers

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

macro "dedup_reduce" : tactic => `(tactic|
  simp [program, assembly, location, Assembly.assemble, Assembly.instructions,
    Assembly.labelOffset, Assembly.Instruction.resolve, Instr.relocate,
    run, step, Comparison.test, Operand.eval, State.put, update, update_shadow, RunResult.prepend,
    Registers.input, count, scratch, random, width, remaining, distinct, size, shift,
    heads, nodes, compact, clearCursor, clearRemaining, seed, temp, key, Registers.hash,
    headAddress, oldHead, cursor, pointer, loaded, compactPointer, newNode, *])

def clearNext (s : State w 64) : State w 64 :=
  ⟨16, update (update s.regs clearCursor (s.regs clearCursor+word w 1))
    clearRemaining (s.regs clearRemaining-word w 1),
    update s.mem (s.regs clearCursor) (word w 0)⟩

theorem clear_iteration (s : State w 64) (rho : RandomMemory w)
    (hp : s.pc = 16) (hn : s.regs clearRemaining ≠ word w 0) :
    Steps program rho 5 s (clearNext s) [.dataWrite (s.regs clearCursor) (word w 0)] := by
  change s.regs (14 : Reg 64) ≠ word w 0 at hn
  apply steps_iff_run.mpr
  unfold clearNext
  dedup_reduce

theorem clear_exit (s : State w 64) (rho : RandomMemory w)
    (hp : s.pc = 16) (hn : s.regs clearRemaining = word w 0) :
    Steps program rho 1 s {s with pc := 21} [] := by
  change s.regs (14 : Reg 64) = word w 0 at hn
  apply steps_iff_run.mpr
  dedup_reduce

def scanAddress (s : State w 64) : Addr w :=
  s.regs nodes + (s.regs cursor-word w 1)*word w 2

def scanMatch (s : State w 64) : State w 64 :=
  ⟨41, update (update s.regs pointer (scanAddress s)) loaded (s.mem (scanAddress s)), s.mem⟩

def scanNext (s : State w 64) : State w 64 :=
  ⟨32, update (update (scanMatch s).regs pointer (scanAddress s+word w 1))
    cursor (s.mem (scanAddress s+word w 1)), s.mem⟩

theorem scan_empty (s : State w 64) (rho : RandomMemory w)
    (hp : s.pc = 32) (hn : s.regs cursor = word w 0) :
    Steps program rho 1 s {s with pc := 44} [] := by
  change s.regs (21 : Reg 64) = word w 0 at hn
  apply steps_iff_run.mpr
  dedup_reduce

theorem scan_match (s : State w 64) (rho : RandomMemory w)
    (hp : s.pc = 32) (hn : s.regs cursor ≠ word w 0)
    (hk : s.regs key = s.mem (scanAddress s)) :
    Steps program rho 6 s (scanMatch s) [.dataRead (scanAddress s) (s.mem (scanAddress s))] := by
  change s.regs (21 : Reg 64) ≠ word w 0 at hn
  change s.regs (17 : Reg 64) = s.mem
    (s.regs (11 : Reg 64)+(s.regs (21 : Reg 64)-word w 1)*word w 2) at hk
  apply steps_iff_run.mpr
  unfold scanMatch scanAddress
  dedup_reduce

theorem scan_miss (s : State w 64) (rho : RandomMemory w)
    (hp : s.pc = 32) (hn : s.regs cursor ≠ word w 0)
    (hk : s.regs key ≠ s.mem (scanAddress s)) :
    Steps program rho 9 s (scanNext s)
      [.dataRead (scanAddress s) (s.mem (scanAddress s)),
       .dataRead (scanAddress s+word w 1) (s.mem (scanAddress s+word w 1))] := by
  change s.regs (21 : Reg 64) ≠ word w 0 at hn
  change s.regs (17 : Reg 64) ≠ s.mem
    (s.regs (11 : Reg 64)+(s.regs (21 : Reg 64)-word w 1)*word w 2) at hk
  apply steps_iff_run.mpr
  unfold scanNext scanMatch scanAddress
  dedup_reduce

def foundNext (s : State w 64) : State w 64 :=
  ⟨25, update (update s.regs Registers.input (s.regs Registers.input+word w 1))
    remaining (s.regs remaining-word w 1), s.mem⟩

theorem found_next (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 41) :
    Steps program rho 3 s (foundNext s) [] := by
  apply steps_iff_run.mpr
  unfold foundNext
  dedup_reduce

def entryNext (s : State w 64) : State w 64 :=
  ⟨5, update (update (update (update (update s.regs heads (s.regs scratch))
    remaining (s.regs count)) distinct (word w 0)) size (word w 1)) shift (s.regs width), s.mem⟩

theorem entry_next (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 0) :
    Steps program rho 5 s (entryNext s) [] := by
  apply steps_iff_run.mpr
  unfold entryNext
  dedup_reduce

def roundNext (s : State w 64) : State w 64 :=
  ⟨5, update (update s.regs size (s.regs size+s.regs size))
    shift (s.regs shift-word w 1), s.mem⟩

theorem round_iteration (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 5)
    (hn : (s.regs size).toNat < (s.regs count).toNat) :
    Steps program rho 4 s (roundNext s) [] := by
  change (s.regs (8 : Reg 64)).toNat < (s.regs (1 : Reg 64)).toNat at hn
  have hn' := Nat.not_le.mpr hn
  apply steps_iff_run.mpr
  unfold roundNext
  dedup_reduce

theorem round_exit (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 5)
    (hn : (s.regs count).toNat ≤ (s.regs size).toNat) :
    Steps program rho 1 s {s with pc := 9} [] := by
  change (s.regs (1 : Reg 64)).toNat ≤ (s.regs (8 : Reg 64)).toNat at hn
  apply steps_iff_run.mpr
  dedup_reduce

def roundedNodes (s : State w 64) : Word w :=
  s.regs heads+(s.regs count+word w 1)*word w 2

def roundedNext (s : State w 64) : State w 64 :=
  ⟨16, update (update (update (update (update s.regs nodes (roundedNodes s))
    temp (s.regs count*word w 2)) compact (roundedNodes s+s.regs count*word w 2))
    clearCursor (s.regs heads)) clearRemaining (s.regs size), s.mem⟩

theorem rounded_next (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 9) :
    Steps program rho 7 s (roundedNext s) [] := by
  apply steps_iff_run.mpr
  unfold roundedNext roundedNodes
  dedup_reduce
  funext r
  simp [update]
  split <;> simp_all [update]

def sampleNext (rho : RandomMemory w) (s : State w 64) : State w 64 :=
  ⟨25, update (update s.regs temp (unsignedMod (rho (s.regs random)) (word w 2)))
    seed (Hashing.MultiplyShift.sample (rho (s.regs random))), s.mem⟩

theorem sample_next (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 21) :
    Steps program rho 4 s (sampleNext rho s)
      [.randomRead (s.regs random) (rho (s.regs random))] := by
  apply steps_iff_run.mpr
  unfold sampleNext Hashing.MultiplyShift.sample
  dedup_reduce
  funext r
  simp [update]
  split <;> simp_all [update]

def inputHash (s : State w 64) : Word w :=
  unsignedShiftRight (s.regs seed*s.mem (s.regs Registers.input)) (s.regs shift)

def inputHead (s : State w 64) : Addr w := s.regs heads+inputHash s

def inputNext (s : State w 64) : State w 64 :=
  ⟨32, update (update (update (update (update s.regs key (s.mem (s.regs Registers.input)))
    Registers.hash (inputHash s)) headAddress (inputHead s))
    oldHead (s.mem (inputHead s))) cursor (s.mem (inputHead s)), s.mem⟩

theorem input_next (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 25)
    (hn : s.regs remaining ≠ word w 0) :
    Steps program rho 7 s (inputNext s)
      [.dataRead (s.regs Registers.input) (s.mem (s.regs Registers.input)),
       .dataRead (inputHead s) (s.mem (inputHead s))] := by
  change s.regs (6 : Reg 64) ≠ word w 0 at hn
  apply steps_iff_run.mpr
  unfold inputNext inputHead inputHash
  dedup_reduce

def finish (s : State w 64) : State w 64 :=
  ⟨56, update (update s.regs Registers.input (s.regs compact)) count (s.regs distinct), s.mem⟩

theorem input_exit (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 25)
    (hn : s.regs remaining = word w 0) :
    TerminatesIn program rho s 4 (finish s) [] := by
  change s.regs (6 : Reg 64) = word w 0 at hn
  apply terminatesIn_iff_run.mpr
  unfold finish
  dedup_reduce

def missingNode (s : State w 64) : Addr w := s.regs distinct*word w 2+s.regs nodes

def missingCompact (s : State w 64) : Addr w := s.regs compact+s.regs distinct

def missingMemory (s : State w 64) : DataMemory w :=
  update (update (update (update s.mem (missingNode s) (s.regs key))
    (missingNode s+word w 1) (s.regs oldHead))
    (missingCompact s) (s.regs key))
    (s.regs headAddress) (s.regs distinct+word w 1)

def missingNext (s : State w 64) : State w 64 :=
  ⟨41, update (update (update s.regs newNode (missingNode s+word w 1))
    compactPointer (missingCompact s)) distinct (s.regs distinct+word w 1), missingMemory s⟩

def missingTrace (s : State w 64) : List (Access w) :=
  [.dataWrite (missingNode s) (s.regs key),
   .dataWrite (missingNode s+word w 1) (s.regs oldHead),
   .dataWrite (missingCompact s) (s.regs key),
   .dataWrite (s.regs headAddress) (s.regs distinct+word w 1)]

theorem missing_next (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 44) :
    Steps program rho 10 s (missingNext s) (missingTrace s) := by
  apply steps_iff_run.mpr
  unfold missingNext missingMemory missingNode missingCompact missingTrace
  dedup_reduce
  exact ⟨rfl,rfl⟩

end Dedup.Blocks
