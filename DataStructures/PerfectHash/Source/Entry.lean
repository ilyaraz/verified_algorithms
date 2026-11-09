import RamLang.Compiler.ExternalEntry
import RamLang.Compiler.EntryRegisters
import WordRam.RegisterEmbedding
import DataStructures.PerfectHash.Admissibility

namespace PerfectHash.Source.Entry
open WordRam RamLang RamLang.Compiler RamLang.ABI
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- The constructor's existing nine input registers, before the stack ABI takes
over. The function is total, while the entry copies exactly indices zero to eight. -/
def argument (i : Nat) : Reg registers := ⟨i % 16,Nat.mod_lt _ (by decide)⟩

/-- The first six words per occurrence plus slack hold deduplication and compact
keys. The remaining supplied scratch is the internally initialized stack. -/
def stack (l : PerfectHash.Layout) (N : Nat) : Region :=
  ⟨l.scratchBase+6*(N+1),58*(N+1)⟩

/-- The internal stack ends at the original scratch reservation's endpoint. -/
theorem stack_end (l : PerfectHash.Layout) (N : Nat) :
    (stack l N).base+(stack l N).size = l.scratchBase+workspaceCapacity N := by
  simp only [stack,workspaceCapacity]
  omega

/-- Existing scratch admissibility suffices for the derived stack region. -/
theorem stack_fits (ha : PerfectHash.Admissible w N l) : (stack l N).Fits w := by
  unfold Region.Fits
  rw [stack_end]
  exact ha.ordinary.scratch

/-- Application scratch and stack are disjoint, with no extra caller argument. -/
theorem stack_separated (l : PerfectHash.Layout) (N : Nat) :
    (Region.mk l.scratchBase (6*(N+1))).Separated (stack l N) := Or.inl (Nat.le_refl _)

/-- All compiler stack effects remain inside the original public reservation. -/
theorem stack_inside (h : (stack l N).Contains (a : Addr w)) : (l.scratch N).Contains a := by
  change l.scratchBase ≤ a.toNat ∧ a.toNat < l.scratchBase+workspaceCapacity N
  rw [← stack_end]
  simp only [Region.Contains,stack] at h ⊢
  omega

/-- The charged prologue computes the stack base while keeping all nine public
arguments live. Registers ten and eleven are outside the public argument range. -/
def locateCode : Code :=
  [.add EntryRegisters.baseRegister (.reg ⟨1,by decide⟩) (.imm 1),
   .mul EntryRegisters.baseRegister (.imm 6) (.reg EntryRegisters.baseRegister),
   .add EntryRegisters.baseRegister (.reg ⟨4,by decide⟩) (.reg EntryRegisters.baseRegister)]

/-- State after the three ordinary arithmetic instructions that locate stack. -/
def located (s : State w registers) : State w registers :=
  ⟨s.pc+3,update s.regs EntryRegisters.baseRegister
    (s.regs ⟨4,by decide⟩+word w 6*(s.regs ⟨1,by decide⟩+word w 1)),s.mem⟩

/-- Each public argument avoids both entry-only scratch registers. -/
theorem argument_ne_scratch (hi : i < 9) :
    argument i ≠ EntryRegisters.addressRegister ∧ argument i ≠ EntryRegisters.baseRegister := by
  constructor <;> intro he
  all_goals have hv := congrArg Fin.val he
  all_goals simp only [argument,EntryRegisters.addressRegister,EntryRegisters.baseRegister,
    Nat.mod_eq_of_lt (by omega : i < 16)] at hv
  all_goals omega

/-- Locating the stack takes exactly three instructions and has no memory event. -/
theorem locate_steps {p : WordRam.Program registers} {rho : RandomMemory w} {s : State w registers}
    (hc : CodeAt p s.pc locateCode) : WordRam.Steps p rho 3 s (located s) [] := by
  let t₁ := s.put EntryRegisters.baseRegister (s.regs ⟨1,by decide⟩+word w 1)
  let t₂ := t₁.put EntryRegisters.baseRegister (word w 6*t₁.regs EntryRegisters.baseRegister)
  have h₁ : WordRam.Step p rho s t₁ none := by
    unfold WordRam.Step WordRam.step
    rw [hc.head]
    rfl
  have h₂ : WordRam.Step p rho t₁ t₂ none := by
    unfold WordRam.Step WordRam.step
    rw [show t₁.pc = s.pc+1 from rfl,hc.tail.head]
    rfl
  have h₃ : WordRam.Step p rho t₂ (located s) none := by
    unfold WordRam.Step WordRam.step
    rw [show t₂.pc = s.pc+2 from rfl,hc.tail.tail.head]
    simp [t₂,t₁,located,Operand.eval,State.put,update,EntryRegisters.baseRegister]
    funext r
    by_cases hr : r = EntryRegisters.baseRegister <;> simp_all [update,EntryRegisters.baseRegister]
  exact .cons h₁ (.cons h₂ (.cons h₃ (.refl _)))

/-- Public parameters survive the calculation of their frame location. -/
theorem located_arguments (s : State w registers) :
    EntryRegisters.entryValues argument (located s) 9 = EntryRegisters.entryValues argument s 9 := by
  apply List.map_congr_left
  intro i hi
  have hb : i < 9 := List.mem_range.mp hi
  exact update_other _ _ _ _ (argument_ne_scratch hb).2

/-- Initialize the saved output-base word and ABI control registers after public
arguments have been copied. The scratch capacity is used before status clobbers it. -/
def readyCode : Code :=
  [.store (.reg EntryRegisters.baseRegister) (.reg limit),
   .add limit (.reg ⟨4,by decide⟩) (.reg ⟨5,by decide⟩),
   .mov sp (.reg EntryRegisters.baseRegister),.mov fp (.imm 0),.mov status (.imm 0)]

/-- The entry-only control transition preserves all copied frame parameters. -/
def ready (s : State w registers) : State w registers :=
  ⟨s.pc+5,update (update (update (update s.regs limit
    (s.regs ⟨4,by decide⟩+s.regs ⟨5,by decide⟩)) sp (s.regs EntryRegisters.baseRegister)) fp (word w 0)) status (word w 0),
    update s.mem (s.regs EntryRegisters.baseRegister) (s.regs limit)⟩

/-- Five charged instructions initialize control state and the saved output-base word. -/
theorem ready_steps {p : WordRam.Program registers} {rho : RandomMemory w} {s : State w registers}
    (hc : CodeAt p s.pc readyCode) : WordRam.Steps p rho 5 s (ready s)
      [.dataWrite (s.regs EntryRegisters.baseRegister) (s.regs limit)] := by
  let t₁ : State w registers := {s with pc := s.pc+1,mem := update s.mem (s.regs EntryRegisters.baseRegister) (s.regs limit)}
  let t₂ := t₁.put limit (t₁.regs ⟨4,by decide⟩+t₁.regs ⟨5,by decide⟩)
  let t₃ := t₂.put sp (t₂.regs EntryRegisters.baseRegister)
  let t₄ := t₃.put fp (word w 0)
  have h₁ : WordRam.Step p rho s t₁ (some (.dataWrite (s.regs EntryRegisters.baseRegister) (s.regs limit))) := by
    unfold WordRam.Step WordRam.step
    rw [hc.head]
    rfl
  have h₂ : WordRam.Step p rho t₁ t₂ none := by
    unfold WordRam.Step WordRam.step
    rw [show t₁.pc = s.pc+1 from rfl,hc.tail.head]
    rfl
  have h₃ : WordRam.Step p rho t₂ t₃ none := by
    unfold WordRam.Step WordRam.step
    rw [show t₂.pc = s.pc+2 from rfl,hc.tail.tail.head]
    rfl
  have h₄ : WordRam.Step p rho t₃ t₄ none := by
    unfold WordRam.Step WordRam.step
    rw [show t₃.pc = s.pc+3 from rfl,hc.tail.tail.tail.head]
    rfl
  have h₅ : WordRam.Step p rho t₄ (ready s) none := by
    unfold WordRam.Step WordRam.step
    rw [show t₄.pc = s.pc+4 from rfl,hc.tail.tail.tail.tail.head]
    simp [ready,t₄,t₃,t₂,t₁,Operand.eval,State.put,update,limit,EntryRegisters.baseRegister]
  exact .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ (.cons h₅ (.refl _)))))

/-- The complete entry prefix copies all original arguments before invoking the
compiled constructor. Function code remains at its original linked address. -/
def setupCode (frame target : Nat) : Code :=
  ((locateCode ++ EntryRegisters.entryArguments argument 9) ++ readyCode) ++ installCode frame target

/-- Setup before the callee prologue has twenty-nine real instructions. -/
theorem setup_length (frame target : Nat) : (setupCode frame target).length = 29 := by rfl

/-- The original nine argument values become source parameters; no seed,
distinct count, initialized workspace, or separate stack pointer is supplied. -/
def values (s : State w registers) : List (Word w) := EntryRegisters.entryValues argument s 9

/-- The charged public setup creates the constructor's frame inside existing
scratch. Callee prologue, copied arguments, saved link and output base are all
physical writes, and every one disappears only under the justified stack trace
projection. Arbitrary other memory and local slots remain dirty. -/
theorem setup {p : WordRam.Program registers} {rho : RandomMemory w} {s : State w registers}
    {f : RamLang.Function} {target : Nat} {l : PerfectHash.Layout} {N : Nat}
    (hc : CodeAt p s.pc (setupCode f.frameSize target)) (hentry : CodeAt p target prologue)
    (ha : PerfectHash.Admissible w N l) (hcount : s.regs ⟨1,by decide⟩ = word w N)
    (hscratch : s.regs ⟨4,by decide⟩ = word w l.scratchBase)
    (hcapacity : s.regs ⟨5,by decide⟩ = word w (workspaceCapacity N))
    (hparams : f.parameters.length = 9) (hspace : f.frameSize ≤ (stack l N).size) :
    ∃ t trace, WordRam.Steps p rho 31 s t trace ∧ t.pc = target+2 ∧
      FrameState (stack l N) (stack l N).base
        ((values s).map some ++ List.replicate f.locals.length none) (s.regs limit) (s.pc+29) s.mem t ∧
      projectTrace (stack l N) trace = [] := by
  let u := located s
  have hu := locate_steps (rho := rho) hc.prefix.prefix.prefix
  have hubase : u.regs EntryRegisters.baseRegister = word w (stack l N).base := by
    dsimp only [u,located]
    rw [update_same,hcount,hscratch,WordRam.word_add,WordRam.word_mul,WordRam.word_add]
    rfl
  have hargsCode : CodeAt p u.pc (EntryRegisters.entryArguments argument 9) := by
    simpa [u,located,locateCode] using hc.prefix.prefix.suffix
  obtain ⟨t,trace,ht,htpc,htregs,htarray,htapp,htproj,_,htbelow⟩ :=
    EntryRegisters.entryArguments_steps (rho := rho) hargsCode (fun i hi => (argument_ne_scratch hi).1)
      hubase (stack_fits ha) (Nat.le_refl _)
      (by
        have h : 11 ≤ f.frameSize := by simp [Function.frameSize,Function.slots,hparams]; omega
        omega)
  have htpc' : t.pc = s.pc+21 := by simpa [u,located] using htpc
  have htbase : t.regs EntryRegisters.baseRegister = word w (stack l N).base :=
    (htregs _ (by decide)).trans hubase
  have htarg (r : Reg registers) (h₁ : r ≠ EntryRegisters.addressRegister)
      (h₂ : r ≠ EntryRegisters.baseRegister) : t.regs r = s.regs r := by
    rw [htregs _ h₁]
    exact update_other _ _ _ _ h₂
  have htlimit : t.regs ⟨4,by decide⟩+t.regs ⟨5,by decide⟩ = word w ((stack l N).base+(stack l N).size) := by
    rw [htarg _ (by decide) (by decide),htarg _ (by decide) (by decide),hscratch,hcapacity,
      WordRam.word_add,stack_end]
  have hreadyCode : CodeAt p t.pc readyCode := by
    rw [htpc']
    simpa [locateCode,EntryRegisters.entryArguments_length] using hc.prefix.suffix
  let v := ready t
  have hv := ready_steps (rho := rho) hreadyCode
  have hvpc : v.pc = s.pc+26 := by simp [v,ready,htpc']
  have hvsp : v.regs sp = word w (stack l N).base := by
    simp [v,ready,update,sp,fp,status,htbase]
  have hvfp : v.regs fp = word w 0 := by simp [v,ready,update,fp,status]
  have hvlimit : v.regs limit = word w ((stack l N).base+(stack l N).size) := by
    simpa [v,ready,update,sp,fp,limit,status] using htlimit
  have hvmem : v.mem = update t.mem (word w (stack l N).base) (t.regs limit) := by simp [v,ready,htbase]
  have hb : (stack l N).base < modulus w := by have h := stack_fits ha; unfold Region.Fits at h; omega
  have hinside : (stack l N).Contains (word w (stack l N).base) := by
    apply Region.contains_index (stack_fits ha) (i := 0)
    simp [stack]
  have hvarray : ArrayAt v.mem ((stack l N).base+2) (values s) := by
    rw [hvmem]
    rw [located_arguments] at htarray
    apply htarray.update_outside
    · have h := stack_fits ha
      unfold Region.Fits at h ⊢
      have hp : 11 ≤ f.frameSize := by simp [Function.frameSize,Function.slots,hparams]; omega
      simp only [values,EntryRegisters.entryValues,List.length_map,List.length_range]
      omega
    · simp only [Region.Contains,word_toNat_of_lt hb]
      omega
  have hvapp : ApplicationMemory (stack l N) s.mem v.mem := by
    intro a hout
    rw [hvmem,update_other]
    · exact htapp a hout
    · intro he
      exact hout (he ▸ hinside)
  have hvsaved : v.mem (word w (stack l N).base) = s.regs limit := by
    rw [hvmem,update_same,htarg _ (by decide) (by decide)]
  have hinstallCode : CodeAt p v.pc (installCode f.frameSize target) := by
    rw [hvpc]
    simpa [locateCode,readyCode,EntryRegisters.entryArguments_length] using hc.suffix
  let z := afterInstall f.frameSize target v
  let out := afterSave 1 link z
  have hz := install_steps (rho := rho) hinstallCode
  have hs := prologue_steps (rho := rho) (s := z) hentry
  have hzfp : z.regs fp = word w (stack l N).base := by
    simp only [z,afterInstall,update_other _ _ _ _ (show fp ≠ link by decide),
      update_other _ _ _ _ (show fp ≠ sp by decide),update_same,hvsp]
  have hzsp : z.regs sp = word w ((stack l N).base+f.frameSize) := by
    simp only [z,afterInstall,update_other _ _ _ _ (show sp ≠ link by decide),update_same,hvsp,WordRam.word_add]
  have hzlimit : z.regs limit = word w ((stack l N).base+(stack l N).size) := by
    simp only [z,afterInstall,update_other _ _ _ _ (show limit ≠ link by decide),
      update_other _ _ _ _ (show limit ≠ sp by decide),update_other _ _ _ _ (show limit ≠ fp by decide),hvlimit]
  have hzlink : z.regs link = word w (s.pc+29) := by
    simp only [z,afterInstall,update_same,hvpc]
  have hslots : ((values s).map some ++ List.replicate f.locals.length (none : Option (Word w))).length = f.slots := by
    simp [values,EntryRegisters.entryValues,Function.slots,hparams]
  have hframe : FrameState (stack l N) (stack l N).base
      ((values s).map some ++ List.replicate f.locals.length none) (s.regs limit) (s.pc+29) s.mem out := by
    apply prologue_frame (stack_fits ha) (Nat.le_refl _) _ hzfp _ hzlimit _ hvsaved hzlink hvapp
    · rw [hslots]; unfold Function.frameSize at hspace; omega
    · rw [hslots]; simpa only [Function.frameSize,Nat.add_assoc] using hzsp
    · exact FrameLocals.parameters hvarray _
  have hlinkInside : (stack l N).Contains (word w ((stack l N).base+1)) :=
    Region.contains_index (stack_fits ha) (by simp [stack]; omega : 1 < (stack l N).size)
  have hsaveProj : projectTrace (stack l N) (saveTrace 1 link z) = [] := by
    simp only [saveTrace,hzfp,WordRam.word_add]
    exact project_stack_write hlinkInside
  have hreadyProj : projectTrace (stack l N) [.dataWrite (t.regs EntryRegisters.baseRegister) (t.regs limit)] = [] := by
    rw [htbase]
    exact project_stack_write hinside
  refine ⟨out,(trace++[.dataWrite (t.regs EntryRegisters.baseRegister) (t.regs limit)])++saveTrace 1 link z,?_,rfl,hframe,?_⟩
  · have hrun := (((hu.trans ht).trans hv).trans hz).trans hs
    simpa only [List.nil_append,List.append_nil] using hrun
  · rw [project_append,project_append,htproj,hreadyProj,hsaveProj]
    rfl

/-- Simulate a complete source constructor invocation through the public entry.
The source proof supplies every algorithmic effect; the adapter adds exactly
thirty-two setup instructions, including its initial jump and callee prologue. -/
theorem invoke {w N : Nat} {source : RamLang.Program} {c : CompiledProgram} {id : FunctionId}
    {f : RamLang.Function} {l : Layout} {rho : RandomMemory w} {s : State w registers}
    {value : Word w} {mem' : DataMemory w} {log : List (Access w)} (suffix : Code)
    (hcompile : compile source = .ok c) (hfit : c.Fits w)
    (hfunction : source.functions[id]? = some f) (hparams : f.parameters.length = 9)
    (hsuffix : 0 < suffix.length)
    (ha : Admissible w N l) (hpc : s.pc = 0)
    (hcount : s.regs ⟨1,by decide⟩ = word w N)
    (hscratch : s.regs ⟨4,by decide⟩ = word w l.scratchBase)
    (hcapacity : s.regs ⟨5,by decide⟩ = word w (workspaceCapacity N))
    (hspace : f.frameSize ≤ (stack l N).size)
    (hcode : (withEntry c.code (setupCode f.frameSize
      ((c.functions[id]?.map FunctionLayout.entry).getD 0) ++ suffix)).size < modulus w)
    (d : Evaluation source rho ((stack l N).size-f.frameSize) f.body
      ((values s).map some ++ List.replicate f.locals.length none) s.mem (.returned value) mem' log)
    (hsep : Separated (stack l N) log) :
    let code := withEntry c.code (setupCode f.frameSize
      ((c.functions[id]?.map FunctionLayout.entry).getD 0) ++ suffix)
    ∃ t trace, WordRam.Steps code rho (32+instructions d) s t trace ∧
      t.pc = c.code.size+29 ∧ t.regs fp = s.regs limit ∧ t.regs sp = word w (stack l N).base ∧
      t.regs result = value ∧ ApplicationMemory (stack l N) mem' t.mem ∧
      projectTrace (stack l N) trace = log := by
  let target := (c.functions[id]?.map FunctionLayout.entry).getD 0
  let adapter := setupCode f.frameSize target ++ suffix
  let code := withEntry c.code adapter
  let u : State w registers := {s with pc := c.code.size}
  have hpositive : 0 < c.code.size := by
    have hh := (Array.getElem?_eq_some_iff.mp (compile_zero hcompile)).1
    omega
  have hjump : WordRam.Step code rho s u none := by
    unfold WordRam.Step WordRam.step
    rw [hpc,withEntry_zero _ _ hpositive]
  have hjumps : WordRam.Steps code rho 1 s u [] := .cons hjump (.refl _)
  have hlinked := withEntry_linked hcompile adapter id f hfunction
  obtain ⟨v,trace₁,hsetup,hvpc,hframe,hproj⟩ := setup (rho := rho) (s := u)
    (withEntry_adapter c.code adapter).prefix hlinked.2.prefix ha hcount hscratch hcapacity hparams hspace
  have hslots : ((values s).map some ++ List.replicate f.locals.length (none : Option (Word w))).length = f.slots := by
    simp [values,EntryRegisters.entryValues,Function.slots,hparams]
  have hret : c.code.size+29 < modulus w := by
    rw [withEntry_size,List.length_append,setup_length] at hcode
    omega
  have himpl := withEntry_evaluation hcompile hfit hcode d hsep
  obtain ⟨t,trace₂,ht⟩ := himpl (stack l N).base (s.regs limit) (c.code.size+29) v hframe
    (by rw [hslots]; unfold Function.frameSize; omega) hret (by rw [hvpc]; exact hlinked.2.suffix)
  obtain ⟨htpc,htfp,htsp,htv,_,htapp⟩ := ht.post
  refine ⟨t,trace₁++trace₂,?_,htpc,htfp,htsp,htv,htapp,?_⟩
  · have hh := (hjumps.trans hsetup).trans ht.execution
    simpa only [List.nil_append] using hh
  · rw [project_append,hproj,ht.projection,List.nil_append]

end PerfectHash.Source.Entry
