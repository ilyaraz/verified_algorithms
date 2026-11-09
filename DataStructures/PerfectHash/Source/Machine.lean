import DataStructures.PerfectHash.Source.Constructor
import DataStructures.PerfectHash.Source.Exit

namespace PerfectHash.Source.Machine
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Bounded
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

/-- Public wrapper for any compiled constructor with the shared source body.
Its code addresses remain those of the final whole-program link. -/
def code (c : CompiledProgram) : WordRam.Program ABI.registers :=
  withEntry c.code (Entry.setupCode 30 ((c.functions[12]?.map FunctionLayout.entry).getD 0) ++
    Entry.finishCode (c.code.size+29))

/-- Entry setup and both exit branches add forty-three static instructions. -/
theorem code_size (c : CompiledProgram) : (code c).size = c.code.size+43 := by
  rw [code,withEntry_size,List.length_append,Entry.setup_length]
  rfl

/-- The public nine-word input before the stack compiler takes over registers. -/
def Input (w N : Nat) (l : Layout) (s : State w ABI.registers) : Prop :=
  s.pc = 0 ∧ Entry.values s = Constructor.arguments w N l

/-- The copied argument vector exposes the input fields needed by the adapter. -/
theorem Input.fields (h : Input w N l s) :
    s.regs ⟨1,by decide⟩ = word w N ∧ s.regs ABI.limit = word w l.outputBase ∧
    s.regs ⟨4,by decide⟩ = word w l.scratchBase ∧ s.regs ⟨5,by decide⟩ = word w (workspaceCapacity N) := by
  have hh := h.2
  change [s.regs ⟨0,by decide⟩,s.regs ⟨1,by decide⟩,s.regs ⟨2,by decide⟩,
    s.regs ⟨3,by decide⟩,s.regs ⟨4,by decide⟩,s.regs ⟨5,by decide⟩,
    s.regs ⟨6,by decide⟩,s.regs ⟨7,by decide⟩,s.regs ⟨8,by decide⟩] = _ at hh
  simp only [Constructor.arguments,List.cons.injEq] at hh
  exact ⟨hh.2.1,hh.2.2.1,hh.2.2.2.2.1,hh.2.2.2.2.2.1⟩

/-- A retained source result lies in output, hence outside every compiler frame. -/
theorem success_inside {xs : List (Word w)} {l : Layout} {value : Word w} {mem : DataMemory w}
    (h : Constructor.Success xs l value mem) :
    ∃ r, r.base = l.outputBase ∧ value = word w (r.base+r.size) ∧
      Table.representation.Holds xs.toFinset r mem ∧ r.size ≤ 64*(xs.toFinset.card+1) ∧
      (∀ addr : Addr w, r.Contains addr → (l.output xs.length).Contains addr) := by
  obtain ⟨r,hb,hv,hr,hs⟩ := h
  refine ⟨r,hb,hv,hr,hs,?_⟩
  intro addr had
  have hd := List.toFinset_card_le xs
  simp only [Region.Contains,hb] at had
  change l.outputBase ≤ addr.toNat ∧ addr.toNat < l.outputBase+64*(xs.length+1)
  omega

/-- Machine success returns the old descriptor registers, the distinct count,
and the algorithm status. The independent runtime status is also successful. -/
def Built (xs : List (Word w)) (l : Layout) (t : State w ABI.registers) : Prop :=
  ∃ r, r.base = l.outputBase ∧ t.regs ABI.sp = word w r.base ∧ t.regs ABI.fp = word w r.size ∧
    t.regs ABI.limit = word w xs.toFinset.card ∧ t.regs Entry.buildStatus = word w 1 ∧
    Table.representation.Holds xs.toFinset r t.mem ∧ r.size ≤ 64*(xs.toFinset.card+1)

/-- Compiler transfer plus the separately charged public wrapper. No target
execution theorem for the original assembly constructor is used. -/
theorem execution {w : Nat} {p : RamLang.Program} {c : CompiledProgram} {rho : RandomMemory w}
    {xs : List (Word w)} {l : Layout} {s : State w ABI.registers} {work : Nat} {failure : Prop}
    (ha : Admissible w xs.length l) (hi : Input w xs.length l s)
    (hcompile : compile p = .ok c) (hfit : c.Fits w) (hcode : (code c).size < modulus w)
    (hfunction : p.functions[12]? = some Bounded.function)
    (hc : Contract p rho ((Entry.stack l xs.length).size-30) Bounded.function.body
      ((Constructor.arguments w xs.length l).map some ++ List.replicate Bounded.function.locals.length none) s.mem
      (fun flow mem' log => ∃ value, flow = .returned value ∧
        ((value = word w 0 ∧ failure) ∨ Constructor.Success xs l value mem') ∧
        (Source.policy w xs.length l).AllowsTrace log ∧
        (RamLang.Library.Retry.randomAddresses log).Sublist
          (consecutiveAddresses w l.randomBase (randomSpan w xs))) work (Constructor.peak xs.length)) :
    ∃ k t trace, WordRam.TerminatesIn (code c) rho s k t trace ∧ k ≤ work+40 ∧
      t.regs ABI.status = word w 1 ∧
      ((t.regs Entry.buildStatus = word w 0 ∧ failure) ∨ Built xs l t) ∧
      (PerfectHash.Bounded.policy w xs.length l).AllowsTrace trace ∧
      (trace.filterMap Access.randomAddress).Sublist (consecutiveAddresses w l.randomBase (randomSpan w xs)) := by
  rw [←hi.2] at hc
  obtain ⟨flow,mem',log,d,⟨value,hv,hout,hp,hr⟩,ht,hs⟩ := hc
  subst flow
  obtain ⟨hcount,houtput,hscratch,hcapacity⟩ := hi.fields
  have hspace : Bounded.function.frameSize ≤ (Entry.stack l xs.length).size := by
    have h := Constructor.stack_sufficient l xs.length
    change 30 ≤ (Entry.stack l xs.length).size
    omega
  obtain ⟨t,trace,hsteps,htpc,htfp,htsp,htvalue,htmem,htproj⟩ :=
    Entry.invoke (Entry.finishCode (c.code.size+29)) hcompile hfit hfunction rfl (by change 0 < 14; decide)
      ha hi.1 hcount hscratch hcapacity hspace hcode d (Source.separated ha hp)
  have hprefix : (PerfectHash.Bounded.policy w xs.length l).AllowsTrace trace :=
    Source.public_policy (projected_policy (by rw [htproj]; exact hp))
  have hrandom : (trace.filterMap Access.randomAddress).Sublist
      (consecutiveAddresses w l.randomBase (randomSpan w xs)) := by
    rw [←project_random_addresses (Entry.stack l xs.length) trace,htproj]
    exact hr
  have hfinish : CodeAt (code c) t.pc (Entry.finishCode t.pc) := by
    rw [htpc]
    exact (withEntry_adapter c.code (Entry.setupCode 30 ((c.functions[12]?.map FunctionLayout.entry).getD 0) ++
      Entry.finishCode (c.code.size+29))).suffix
  rcases hout with ⟨rfl,hfailure⟩ | hsuccess
  · have hterm := hsteps.then_terminates (Entry.failure_terminates hfinish htvalue)
    have ho := Entry.failed_output t
    exact ⟨_,_,_,hterm,by omega,ho.2.2.2.2.1,Or.inl ⟨ho.2.2.2.1,hfailure⟩,
      by simpa using hprefix,by simpa using hrandom⟩
  · have hnonzero := hsuccess.nonzero
    have hterm := hsteps.then_terminates (Entry.finish_terminates hfinish (by rwa [htvalue]))
    obtain ⟨r,hbase,hvalue,hrep,hsize,hinside⟩ := success_inside hsuccess
    have hrep' : Table.representation.Holds xs.toFinset r t.mem := by
      apply Table.representation.locality hrep
      intro addr had
      exact (htmem addr (Region.not_contains_of_separated ha.ordinary.output_scratch
        (hinside addr had) ∘ Entry.stack_inside)).symm
    obtain ⟨table,hview⟩ := hrep'
    have hheader : t.mem (t.regs ABI.fp+word w 3) = word w xs.toFinset.card := by
      rw [htfp,houtput,WordRam.word_add,←hbase]
      exact hview.headerCount
    have hextent : value-word w l.outputBase = word w r.size := by
      rw [hvalue,←hbase,WordRam.word_sub _ _ (by have hf := hview.fits; unfold Region.Fits at hf; omega) (by omega)]
      simp
    have ho := Entry.finished_output t
    refine ⟨_,_,_,hterm,by omega,ho.2.2.2.2.1,Or.inr ?_,?_,?_⟩
    · refine ⟨r,hbase,?_,?_,?_,ho.2.2.2.1,?_,hsize⟩
      · rw [ho.1,htfp,houtput,hbase]
      · rw [ho.2.1,htvalue,htfp,houtput,hextent]
      · rw [ho.2.2.1,hheader]
      · rw [ho.2.2.2.2.2]
        exact ⟨table,hview⟩
    · apply (AccessPolicy.allowsTrace_append _).mpr
      refine ⟨hprefix,?_⟩
      intro e he
      simp only [List.mem_singleton] at he
      subst e
      apply Or.inr ∘ Or.inl
      rw [htfp,houtput,WordRam.word_add]
      exact Source.header_inside ha (by decide : 3 < 4)
    · simpa [List.filterMap_append,Access.randomAddress] using hrandom

end PerfectHash.Source.Machine
