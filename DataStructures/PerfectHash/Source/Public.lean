import DataStructures.PerfectHash.Source.Machine

namespace PerfectHash.Source.Public
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Bounded

/-- Preserve public input and descriptor registers and map the auxiliary
algorithm status to the original register eighteen. -/
def embed (r : Reg ABI.registers) : Reg StaticSet.registerCount :=
  if r.val = 14 then ⟨18,by decide⟩ else ⟨r.val,Nat.lt_trans r.isLt (by decide : ABI.registers < StaticSet.registerCount)⟩

/-- The fixed embedding has no register aliases. -/
theorem embed_injective : Function.Injective embed := by decide

/-- One fixed sixty-four-register program, with no added execution machinery. -/
def program (c : CompiledProgram) : WordRam.Program StaticSet.registerCount :=
  ((Machine.code c).toList.map (Instr.rename embed)).toArray

/-- The axiom-free list implementation agrees with array register renaming. -/
theorem program_eq (c : CompiledProgram) : program c = (Machine.code c).map (Instr.rename embed) := by
  simp [program,←Array.toList_map]

/-- Register embedding does not add code or instruction work. -/
theorem program_size (c : CompiledProgram) : (program c).size = c.code.size+43 := by
  simp only [program_eq,Array.size_map,Machine.code_size]

/-- The original nine-register calling convention initializes the source entry
without any additional stack, seed, or distinct-count argument. -/
theorem input {w N : Nat} {l : Layout} {s : State w StaticSet.registerCount} (hin : BuildInput w N l s.regs) (hpc : s.pc = 0) :
    Machine.Input w N l (s.project embed) := by
  refine ⟨hpc,?_⟩
  change [s.regs ⟨0,by decide⟩,s.regs ⟨1,by decide⟩,s.regs ⟨2,by decide⟩,
    s.regs ⟨3,by decide⟩,s.regs ⟨4,by decide⟩,s.regs ⟨5,by decide⟩,
    s.regs ⟨6,by decide⟩,s.regs ⟨7,by decide⟩,s.regs ⟨8,by decide⟩] = _
  rcases hin with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  simp only [h0,h1,h2,h3,h4,h5,h6,h7,h8,Constructor.arguments]

/-- Success in the original descriptor and algorithm-status convention. -/
def Built (xs : List (Word w)) (l : Layout) (s : State w StaticSet.registerCount) : Prop :=
  Machine.Built xs l (s.project embed)

/-- Projected success exposes the original public descriptor and count. -/
theorem Built.descriptor {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w StaticSet.registerCount} (h : Built xs l s) :
    Table.representation.Holds xs.toFinset (StaticSet.readDescriptor s.regs) s.mem ∧
      (StaticSet.readDescriptor s.regs).base = l.outputBase ∧
      (StaticSet.readDescriptor s.regs).size ≤ 64*(xs.toFinset.card+1) ∧
      s.regs ⟨2,by decide⟩ = word w xs.toFinset.card ∧ s.regs ⟨18,by decide⟩ = word w 1 := by
  obtain ⟨r,hb,h0,h1,h2,hstatus,hrep,hsize⟩ := h
  have hf := Table.representation.fits hrep
  have hdesc : StaticSet.readDescriptor s.regs = r := by
    change s.regs ⟨0,by decide⟩ = word w r.base at h0
    change s.regs ⟨1,by decide⟩ = word w r.size at h1
    unfold StaticSet.readDescriptor
    rw [h0,h1,word_toNat_of_lt (by unfold Region.Fits at hf; omega : r.base < modulus w),
      word_toNat_of_lt (by unfold Region.Fits at hf; omega : r.size < modulus w)]
  exact ⟨hdesc ▸ hrep,by rw [hdesc]; exact hb,by rw [hdesc]; exact hsize,h2,hstatus⟩

/-- The source constructor contract yields a real execution of the public
program. Runtime status one distinguishes all ordinary algorithm outcomes from
stack exhaustion, and the full trace includes physical stack traffic. -/
theorem execution {w : Nat} {p : RamLang.Program} {c : CompiledProgram} {rho : RandomMemory w}
    {xs : List (Word w)} {l : Layout} {s : State w StaticSet.registerCount} {work : Nat} {failure : Prop}
    (ha : Admissible w xs.length l) (hpc : s.pc = 0) (hin : BuildInput w xs.length l s.regs)
    (hcompile : compile p = .ok c) (hfit : c.Fits w) (hcode : (Machine.code c).size < modulus w)
    (hfunction : p.functions[12]? = some Bounded.function)
    (hc : Contract p rho ((Entry.stack l xs.length).size-30) Bounded.function.body
      ((Constructor.arguments w xs.length l).map some ++ List.replicate Bounded.function.locals.length none) s.mem
      (fun flow mem' log => ∃ value, flow = .returned value ∧
        ((value = word w 0 ∧ failure) ∨ Constructor.Success xs l value mem') ∧
        (Source.policy w xs.length l).AllowsTrace log ∧
        (RamLang.Library.Retry.randomAddresses log).Sublist
          (consecutiveAddresses w l.randomBase (randomSpan w xs))) work (Constructor.peak xs.length)) :
    ∃ k t trace, WordRam.TerminatesIn (program c) rho s k t trace ∧ k ≤ work+40 ∧
      t.regs ⟨5,by decide⟩ = word w 1 ∧
      ((t.regs ⟨18,by decide⟩ = word w 0 ∧ failure) ∨ Built xs l t) ∧
      (PerfectHash.Bounded.policy w xs.length l).AllowsTrace trace ∧
      (trace.filterMap Access.randomAddress).Sublist (consecutiveAddresses w l.randomBase (randomSpan w xs)) := by
  obtain ⟨k,t,trace,ht,hk,hstatus,hpost,hpolicy,hrandom⟩ :=
    Machine.execution ha (input hin hpc) hcompile hfit hcode hfunction hc
  obtain ⟨u,hu,hproject⟩ := ht.rename embed embed_injective
  refine ⟨k,u,trace,by simpa only [program_eq] using hu,hk,?_,?_,hpolicy,hrandom⟩
  · have hh := congrArg (fun s => s.regs ABI.status) hproject
    exact hh.trans hstatus
  · rcases hpost with ⟨hfail,hwhy⟩ | hbuilt
    · have hh := congrArg (fun s => s.regs Entry.buildStatus) hproject
      exact Or.inl ⟨hh.trans hfail,hwhy⟩
    · exact Or.inr (by unfold Built; rw [hproject]; exact hbuilt)

end PerfectHash.Source.Public
