import DataStructures.PerfectHash.Source.Entry

namespace PerfectHash.Source.Entry
open WordRam RamLang RamLang.Compiler RamLang.ABI

/-- This auxiliary result flag is embedded into the original public status
register eighteen. It is distinct from the source runtime status register. -/
def buildStatus : Reg registers := ⟨14,by decide⟩

/-- Decode the source return into the original descriptor registers. The frame
return restored the saved output base into fp. Zero denotes budget failure. -/
def finishCode (pc : Nat) : Code :=
  [.branch .eq (.reg result) (.imm 0) (pc+8),
   .mov sp (.reg fp),.sub fp (.reg result) (.reg sp),
   .add address (.reg sp) (.imm 3),.load limit (.reg address),
   .mov buildStatus (.imm 1),.mov status (.imm 1),.halt,
   .mov sp (.imm 0),.mov fp (.imm 0),.mov limit (.imm 0),
   .mov buildStatus (.imm 0),.mov status (.imm 1),.halt]

/-- State after a successful descriptor decode, before the charged halt. -/
def finished (s : State w registers) : State w registers :=
  let t : State w registers := {s with pc := s.pc+1}
  let t := t.put sp (t.regs fp)
  let t := t.put fp (t.regs result-t.regs sp)
  let t := t.put address (t.regs sp+word w 3)
  let t := t.put limit (t.mem (t.regs address))
  let t := t.put buildStatus (word w 1)
  t.put status (word w 1)

/-- Budget failure clears the returned descriptor and distinct count. -/
def failed (s : State w registers) : State w registers :=
  let t : State w registers := {s with pc := s.pc+8}
  let t := t.put sp (word w 0)
  let t := t.put fp (word w 0)
  let t := t.put limit (word w 0)
  let t := t.put buildStatus (word w 0)
  t.put status (word w 1)

/-- Successful decoding takes eight instructions, including the one header read and halt. -/
theorem finish_terminates {p : WordRam.Program registers} {rho : RandomMemory w} {s : State w registers}
    (hc : CodeAt p s.pc (finishCode s.pc)) (hv : s.regs result ≠ word w 0) :
    WordRam.TerminatesIn p rho s 8 (finished s) [.dataRead (s.regs fp+word w 3) (s.mem (s.regs fp+word w 3))] := by
  have h0 : p[s.pc+0]? = some (.branch .eq (.reg result) (.imm 0) (s.pc+8)) := hc 0 _ rfl
  have h1 : p[s.pc+1]? = some (.mov sp (.reg fp)) := hc 1 _ rfl
  have h2 : p[s.pc+2]? = some (.sub fp (.reg result) (.reg sp)) := hc 2 _ rfl
  have h3 : p[s.pc+3]? = some (.add address (.reg sp) (.imm 3)) := hc 3 _ rfl
  have h4 : p[s.pc+4]? = some (.load limit (.reg address)) := hc 4 _ rfl
  have h5 : p[s.pc+5]? = some (.mov buildStatus (.imm 1)) := hc 5 _ rfl
  have h6 : p[s.pc+6]? = some (.mov status (.imm 1)) := hc 6 _ rfl
  have h7 : p[s.pc+7]? = some (.halt) := hc 7 _ rfl
  simp only [Nat.add_zero] at h0
  have hr : WordRam.run p rho 8 s = ⟨finished s,8,[.dataRead (s.regs fp+word w 3) (s.mem (s.regs fp+word w 3))],.halted⟩ := by
    simp [WordRam.run,WordRam.step,h0,h1,h2,h3,h4,h5,h6,h7,hv,Comparison.test,Operand.eval,State.put,
      update,sp,fp,result,address,limit,status,buildStatus,WordRam.RunResult.prepend,finished,Nat.add_assoc]
  have hh := terminatesIn_of_halted (p := p) (rho := rho) (s := s) (fuel := 8) (by rw [hr])
  simpa only [hr] using hh

/-- Budget decoding takes seven instructions and accesses no memory. -/
theorem failure_terminates {p : WordRam.Program registers} {rho : RandomMemory w} {s : State w registers}
    (hc : CodeAt p s.pc (finishCode s.pc)) (hv : s.regs result = word w 0) :
    WordRam.TerminatesIn p rho s 7 (failed s) [] := by
  have h0 : p[s.pc+0]? = some (.branch .eq (.reg result) (.imm 0) (s.pc+8)) := hc 0 _ rfl
  have h8 : p[s.pc+8]? = some (.mov sp (.imm 0)) := hc 8 _ rfl
  have h9 : p[s.pc+9]? = some (.mov fp (.imm 0)) := hc 9 _ rfl
  have h10 : p[s.pc+10]? = some (.mov limit (.imm 0)) := hc 10 _ rfl
  have h11 : p[s.pc+11]? = some (.mov buildStatus (.imm 0)) := hc 11 _ rfl
  have h12 : p[s.pc+12]? = some (.mov status (.imm 1)) := hc 12 _ rfl
  have h13 : p[s.pc+13]? = some (.halt) := hc 13 _ rfl
  simp only [Nat.add_zero] at h0
  have hr : WordRam.run p rho 7 s = ⟨failed s,7,[],.halted⟩ := by
    simp [WordRam.run,WordRam.step,h0,h8,h9,h10,h11,h12,h13,hv,Comparison.test,Operand.eval,State.put,
      update,sp,fp,result,address,limit,status,buildStatus,WordRam.RunResult.prepend,failed,Nat.add_assoc]
  have hh := terminatesIn_of_halted (p := p) (rho := rho) (s := s) (fuel := 7) (by rw [hr])
  simpa only [hr] using hh

/-- Success returns base, retained extent, computed distinct count and status,
preserving all ordinary memory during the final decode. -/
theorem finished_output (s : State w registers) :
    (finished s).regs sp = s.regs fp ∧ (finished s).regs fp = s.regs result-s.regs fp ∧
    (finished s).regs limit = s.mem (s.regs fp+word w 3) ∧ (finished s).regs buildStatus = word w 1 ∧
    (finished s).regs status = word w 1 ∧ (finished s).mem = s.mem := by
  simp [finished,State.put,update,sp,fp,result,address,limit,status,buildStatus]

/-- Failure is an ordinary successful runtime return with algorithm status zero. -/
theorem failed_output (s : State w registers) :
    (failed s).regs sp = word w 0 ∧ (failed s).regs fp = word w 0 ∧ (failed s).regs limit = word w 0 ∧
    (failed s).regs buildStatus = word w 0 ∧ (failed s).regs status = word w 1 ∧ (failed s).mem = s.mem := by
  simp [failed,State.put,update,sp,fp,limit,status,buildStatus]

end PerfectHash.Source.Entry
