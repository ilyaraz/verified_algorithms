import RamLang.Semantics

namespace RamLang
open WordRam

variable {w dst : Nat} {rho : RandomMemory w} {locals locals' : Locals w}
  {mem mem' : DataMemory w} {event : Option (Access w)} {x y : Atom} {op : Binary}

/-- A successful local update is an in-bounds list replacement. -/
theorem writeLocal_ok {v : Word w} (h : writeLocal locals dst v = .ok locals') :
    dst < locals.length ∧ locals' = locals.set dst (some v) := by
  unfold writeLocal at h
  split at h
  · rename_i hb
    cases h
    exact ⟨hb, rfl⟩
  · cases h

theorem writeLocal_preserves_length {v : Word w} (h : writeLocal locals dst v = .ok locals') :
    locals'.length = locals.length := by
  rw [(writeLocal_ok h).2]
  exact List.length_set

/-- Successful source assignment exposes the old-operand value and checked local update. -/
theorem Primitive.move_ok (h : Primitive.eval rho locals mem (.move dst x) = .ok (locals',mem',event)) :
    ∃ v, x.eval locals = .ok v ∧ writeLocal locals dst v = .ok locals' ∧ mem' = mem ∧ event = none := by
  cases hx : x.eval locals with
  | error e => simp [Primitive.eval, hx, bind, Except.bind] at h
  | ok v =>
    cases hw : writeLocal locals dst v with
    | error e => simp [Primitive.eval, hx, hw, bind, Except.bind] at h
    | ok result =>
      simp [Primitive.eval, hx, hw, bind, pure, Except.bind, Except.pure] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨v, rfl, hw, rfl, rfl⟩

theorem Primitive.binary_ok
    (h : Primitive.eval rho locals mem (.binary dst op x y) = .ok (locals',mem',event)) :
    ∃ a b, x.eval locals = .ok a ∧ y.eval locals = .ok b ∧
      writeLocal locals dst (op.eval a b) = .ok locals' ∧ mem' = mem ∧ event = none := by
  cases hx : x.eval locals with
  | error e => simp [Primitive.eval, hx, bind, Except.bind] at h
  | ok a =>
    cases hy : y.eval locals with
    | error e => simp [Primitive.eval, hx, hy, bind, Except.bind] at h
    | ok b =>
      cases hw : writeLocal locals dst (op.eval a b) with
      | error e => simp [Primitive.eval, hx, hy, hw, bind, Except.bind] at h
      | ok result =>
        simp [Primitive.eval, hx, hy, hw, bind, pure, Except.bind, Except.pure] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact ⟨a, b, rfl, rfl, hw, rfl, rfl⟩

theorem Primitive.load_ok
    (h : Primitive.eval rho locals mem (.load dst x) = .ok (locals',mem',event)) :
    ∃ a, x.eval locals = .ok a ∧ writeLocal locals dst (mem a) = .ok locals' ∧
      mem' = mem ∧ event = some (.dataRead a (mem a)) := by
  cases hx : x.eval locals with
  | error e => simp [Primitive.eval, hx, bind, Except.bind] at h
  | ok a =>
    cases hw : writeLocal locals dst (mem a) with
    | error e => simp [Primitive.eval, hx, hw, bind, Except.bind] at h
    | ok result =>
      simp [Primitive.eval, hx, hw, bind, pure, Except.bind, Except.pure] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨a, rfl, hw, rfl, rfl⟩

theorem Primitive.random_ok
    (h : Primitive.eval rho locals mem (.random dst x) = .ok (locals',mem',event)) :
    ∃ a, x.eval locals = .ok a ∧ writeLocal locals dst (rho a) = .ok locals' ∧
      mem' = mem ∧ event = some (.randomRead a (rho a)) := by
  cases hx : x.eval locals with
  | error e => simp [Primitive.eval, hx, bind, Except.bind] at h
  | ok a =>
    cases hw : writeLocal locals dst (rho a) with
    | error e => simp [Primitive.eval, hx, hw, bind, Except.bind] at h
    | ok result =>
      simp [Primitive.eval, hx, hw, bind, pure, Except.bind, Except.pure] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨a, rfl, hw, rfl, rfl⟩

theorem Primitive.store_ok
    (h : Primitive.eval rho locals mem (.store x y) = .ok (locals',mem',event)) :
    ∃ a v, x.eval locals = .ok a ∧ y.eval locals = .ok v ∧
      locals' = locals ∧ mem' = update mem a v ∧ event = some (.dataWrite a v) := by
  cases hx : x.eval locals with
  | error e => simp [Primitive.eval, hx, bind, Except.bind] at h
  | ok a =>
    cases hy : y.eval locals with
    | error e => simp [Primitive.eval, hx, hy, bind, Except.bind] at h
    | ok v =>
      simp [Primitive.eval, hx, hy, bind, pure, Except.bind, Except.pure] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨a, v, rfl, rfl, rfl, rfl, rfl⟩

/-- Local storage remains fixed-size throughout a successful primitive. -/
theorem Primitive.length (h : Primitive.eval rho locals mem operation = .ok (locals',mem',event)) :
    locals'.length = locals.length := by
  have assigned {dst : Nat} {v} (h : writeLocal locals dst v = .ok locals') : locals'.length = locals.length := by
    unfold writeLocal at h
    split at h
    · cases h; exact List.length_set
    · cases h
  cases operation with
  | move d x => obtain ⟨_,_,hw,_,_⟩ := Primitive.move_ok h; exact assigned hw
  | binary d op x y => obtain ⟨_,_,_,_,hw,_,_⟩ := Primitive.binary_ok h; exact assigned hw
  | load d a => obtain ⟨_,_,hw,_,_⟩ := Primitive.load_ok h; exact assigned hw
  | random d a => obtain ⟨_,_,hw,_,_⟩ := Primitive.random_ok h; exact assigned hw
  | store a x => obtain ⟨_,_,_,_,rfl,_,_⟩ := Primitive.store_ok h; rfl

end RamLang
