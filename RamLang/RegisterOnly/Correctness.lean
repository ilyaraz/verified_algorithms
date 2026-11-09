import RamLang.RegisterOnly.Simulation
import RamLang.Logic.Contract
import RamLang.Logic.Frame
import WordRam.Blocks

namespace RamLang.RegisterOnly
open WordRam Compiler

/-- Public arguments occupy the entry function's first placed local registers. -/
def entryValues (c : Compiled capacity) (s : State w (capacity+2)) : List (Word w) :=
  (List.range c.entry.parameters.length).map (fun i => s.regs (slot capacity 0 i))

/-- Initial register arguments represent initialized source parameters while
all remaining source locals may correspond to arbitrary dirty registers. -/
theorem entry_locals (c : Compiled capacity) (s : State w (capacity+2)) :
    LocalsAt s.regs 0 ((entryValues c s).map some ++ List.replicate c.entry.locals.length none) := by
  apply ValuesAt.locals
  intro i value hi
  obtain ⟨hb,hvalue⟩ := List.getElem?_eq_some_iff.mp hi
  simp only [entryValues,List.length_map,List.length_range] at hb
  simpa [entryValues,Nat.zero_add] using hvalue

/-- The public success continuation costs exactly two instructions and accesses
neither ordinary nor random memory. -/
theorem finish_terminates {capacity : Nat} {p : WordRam.Program (capacity+2)}
    {rho : RandomMemory w} {s : State w (capacity+2)} (hc : CodeAt p s.pc (finish capacity)) :
    WordRam.TerminatesIn p rho s 2 (s.put (status capacity) (word w 1)) [] := by
  have hs : WordRam.Step p rho s (s.put (status capacity) (word w 1)) none := by
    unfold WordRam.Step WordRam.step
    rw [hc.head]
    rfl
  refine ⟨1,rfl,.cons hs (.refl _),?_⟩
  unfold WordRam.step
  rw [show (s.put (status capacity) (word w 1)).pc = s.pc+1 from rfl,hc.tail.head]

/-- A checked register-only program implements its successful source proof in
exactly its code length, including halt. The complete application trace and
ordinary memory are preserved without a stack reservation or trace projection. -/
theorem compiled_returns {capacity free : Nat} {source : Program} {c : Compiled capacity}
    {rho : RandomMemory w} {s : State w (capacity+2)} {value : Word w}
    {mem' : DataMemory w} {trace : List (Access w)}
    (hc : compile capacity source = .ok c) (hpc : s.pc = 0)
    (d : Evaluation source rho free c.entry.body
      ((entryValues c s).map some ++ List.replicate c.entry.locals.length none)
      s.mem (.returned value) mem' trace) :
    ∃ t, WordRam.TerminatesIn c.code rho s c.code.size t trace ∧
      t.regs (result capacity) = value ∧ t.regs (status capacity) = word w 1 ∧ t.mem = mem' := by
  obtain ⟨_,_,hsource,hlinked,hbudget⟩ := compile_sound hc
  have hcode := CodeAt.toArray (c.plan.code capacity c.entry.slots ++ finish capacity)
  have hbody : CodeAt c.code s.pc (c.plan.code capacity c.entry.slots) := by rw [hpc]; exact hcode.prefix
  obtain ⟨t,hs,htpc,htvalue,htmem⟩ := plan_steps c.plan hlinked hbudget
    (by simp [entryValues,Function.slots]) (entry_locals c s) hbody (by rw [hsource]; exact d)
  have hfinish : CodeAt c.code t.pc (finish capacity) := by rw [htpc,hpc]; exact hcode.suffix
  have hterm := hs.then_terminates (finish_terminates hfinish)
  refine ⟨t.put (status capacity) (word w 1),?_,?_,?_,htmem⟩
  · simpa [Compiled.code,finish,List.length_append] using hterm
  · simpa [State.put,update,result,status,Fin.ext_iff] using htvalue
  · simp [State.put]

/-- Source contracts transfer directly to the alternate backend. Its exact
instruction count is read from the emitted code, and source trace policies
apply to every interrupted prefix without adding compiler memory permissions. -/
theorem contract {capacity free work peak : Nat} {source : Program} {c : Compiled capacity}
    {rho : RandomMemory w} {s : State w (capacity+2)}
    {Q : Word w → DataMemory w → List (Access w) → Prop} {policy : AccessPolicy w}
    (hc : compile capacity source = .ok c) (hpc : s.pc = 0)
    (h : Logic.Contract source rho free c.entry.body
      ((entryValues c s).map some ++ List.replicate c.entry.locals.length none) s.mem
      (fun flow mem' trace => ∃ value, flow = .returned value ∧ Q value mem' trace ∧ policy.AllowsTrace trace) work peak) :
    ∃ t value mem' trace, WordRam.TerminatesIn c.code rho s c.code.size t trace ∧
      t.regs (result capacity) = value ∧ t.regs (status capacity) = word w 1 ∧ t.mem = mem' ∧
      Q value mem' trace ∧ ∀ fuel, policy.AllowsTrace (WordRam.run c.code rho fuel s).trace := by
  obtain ⟨flow,mem',trace,d,⟨value,rfl,hq,hpolicy⟩,_,_⟩ := h
  obtain ⟨t,ht,hresult,hstatus,hmem⟩ := compiled_returns hc hpc d
  exact ⟨t,value,mem',trace,ht,hresult,hstatus,hmem,hq,fun fuel => ht.prefix_policy hpolicy fuel⟩

/-- A read-only source proof yields a genuinely read-only machine execution:
application memory is unchanged and no interrupted prefix contains a write. -/
theorem compiled_readOnly {capacity free : Nat} {source : Program} {c : Compiled capacity}
    {rho : RandomMemory w} {s : State w (capacity+2)} {value : Word w}
    {mem' : DataMemory w} {trace : List (Access w)}
    (hc : compile capacity source = .ok c) (hpc : s.pc = 0)
    (d : Evaluation source rho free c.entry.body
      ((entryValues c s).map some ++ List.replicate c.entry.locals.length none)
      s.mem (.returned value) mem' trace)
    (readonly : ∀ a v, .dataWrite a v ∉ trace) :
    ∃ t, WordRam.TerminatesIn c.code rho s c.code.size t trace ∧
      t.regs (result capacity) = value ∧ t.mem = s.mem ∧
      ∀ fuel a v, .dataWrite a v ∉ (WordRam.run c.code rho fuel s).trace := by
  obtain ⟨t,ht,hresult,_,hmem⟩ := compiled_returns hc hpc d
  have hm : mem' = s.mem := by funext a; exact d.frame a (readonly a)
  let policy : AccessPolicy w := ⟨fun _ => True,fun _ => False,fun _ => True⟩
  have hp : policy.AllowsTrace trace := by
    intro e he
    cases e with
    | dataRead _ _ | randomRead _ _ => trivial
    | dataWrite a v => exact readonly a v he
  refine ⟨t,ht,hresult,hmem.trans hm,?_⟩
  intro fuel a v he
  exact ht.prefix_policy hp fuel (.dataWrite a v) he

end RamLang.RegisterOnly
