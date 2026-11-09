import RamLang.RegisterOnly.Compile

namespace RamLang.RegisterOnly
open WordRam

/-- A physical register outside a placed local interval. -/
def Outside (capacity base count : Nat) (r : Reg (capacity+2)) : Prop :=
  ∀ i, i < count → r ≠ slot capacity base i

/-- An instruction sequence preserves all registers outside an allocated
interval; this includes live caller values while an inline helper executes. -/
def Preserves (before after : Registers w (capacity+2)) (base count : Nat) : Prop :=
  ∀ r, Outside capacity base count r → after r = before r

/-- Updating a checked local slot preserves every outside register. -/
theorem preserves_update {capacity base count dst : Nat} (regs : Registers w (capacity+2))
    (value : Word w) (hd : dst < count) :
    Preserves regs (update regs (slot capacity base dst) value) base count :=
  fun r hr => update_other _ _ _ _ (hr dst hd)

/-- Register-frame preservation composes over successive execution fragments. -/
theorem Preserves.trans {capacity base count : Nat} {a b c : Registers w (capacity+2)}
    (h : Preserves a b base count) (g : Preserves b c base count) : Preserves a c base count :=
  fun r hr => (g r hr).trans (h r hr)

/-- Every successful source primitive is implemented by exactly one machine
instruction with exactly the source access event, including operand aliasing.
There are no compiler memory events to erase. -/
theorem primitive_step {capacity base : Nat} {p : WordRam.Program (capacity+2)} {rho : RandomMemory w}
    {s : State w (capacity+2)} {op : Primitive} {locals out : Locals w}
    {mem' : DataMemory w} {event : Option (Access w)}
    (hc : p[s.pc]? = some (primitive capacity base op)) (hf : Fits capacity base locals.length)
    (hl : LocalsAt s.regs base locals) (he : op.eval rho locals s.mem = .ok (out,mem',event)) :
    ∃ t, WordRam.Step p rho s t event ∧ t.pc = s.pc+1 ∧ LocalsAt t.regs base out ∧ t.mem = mem' ∧
      Preserves s.regs t.regs base locals.length := by
  cases op with
  | move dst a =>
    obtain ⟨v,hv,hw,hm,hevent⟩ := Primitive.move_ok he
    subst mem' event
    refine ⟨s.put (slot capacity base dst) v,?_,rfl,hl.write hf hw,rfl,
      preserves_update s.regs v (writeLocal_ok hw).1⟩
    unfold WordRam.Step WordRam.step
    rw [hc]
    simp only [primitive,atom_value hl hv]
  | binary dst op a b =>
    obtain ⟨x,y,hx,hy,hw,hm,hevent⟩ := Primitive.binary_ok he
    subst mem' event
    refine ⟨s.put (slot capacity base dst) (op.eval x y),?_,rfl,hl.write hf hw,rfl,
      preserves_update s.regs _ (writeLocal_ok hw).1⟩
    unfold WordRam.Step WordRam.step
    rw [hc]
    cases op <;> simp only [primitive,Binary.eval,atom_value hl hx,atom_value hl hy]
  | load dst address =>
    obtain ⟨a,ha,hw,hm,hevent⟩ := Primitive.load_ok he
    subst mem' event
    refine ⟨s.put (slot capacity base dst) (s.mem a),?_,rfl,hl.write hf hw,rfl,
      preserves_update s.regs _ (writeLocal_ok hw).1⟩
    unfold WordRam.Step WordRam.step
    rw [hc]
    simp only [primitive,atom_value hl ha]
  | random dst address =>
    obtain ⟨a,ha,hw,hm,hevent⟩ := Primitive.random_ok he
    subst mem' event
    refine ⟨s.put (slot capacity base dst) (rho a),?_,rfl,hl.write hf hw,rfl,
      preserves_update s.regs _ (writeLocal_ok hw).1⟩
    unfold WordRam.Step WordRam.step
    rw [hc]
    simp only [primitive,atom_value hl ha]
  | store address value =>
    obtain ⟨a,v,ha,hv,hout,hm,hevent⟩ := Primitive.store_ok he
    subst out mem' event
    refine ⟨{s with pc := s.pc+1,mem := update s.mem a v},?_,rfl,hl,rfl,fun _ _ => rfl⟩
    unfold WordRam.Step WordRam.step
    rw [hc]
    simp only [primitive,atom_value hl ha,atom_value hl hv]

end RamLang.RegisterOnly
