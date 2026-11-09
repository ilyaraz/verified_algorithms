import RamLang.Logic.Contract

namespace RamLang
open WordRam

/-- A source primitive preserves each ordinary memory cell absent from its
write event, including when it loads random memory at the same numeric address. -/
theorem Primitive.frame {w : Nat} {rho : RandomMemory w} {locals out : Locals w}
    {mem mem' : DataMemory w} {op : Primitive} {event : Option (Access w)} {protectedCell : Addr w}
    (h : op.eval rho locals mem = .ok (out,mem',event))
    (safe : ∀ value, .dataWrite protectedCell value ∉ event.toList) :
    mem' protectedCell = mem protectedCell := by
  cases op with
  | move => obtain ⟨_,_,_,hm,_⟩ := Primitive.move_ok h; rw [hm]
  | binary => obtain ⟨_,_,_,_,_,hm,_⟩ := Primitive.binary_ok h; rw [hm]
  | load => obtain ⟨_,_,_,hm,_⟩ := Primitive.load_ok h; rw [hm]
  | random => obtain ⟨_,_,_,hm,_⟩ := Primitive.random_ok h; rw [hm]
  | store =>
    obtain ⟨address,value,_,_,_,hm,he⟩ := Primitive.store_ok h
    have ha : protectedCell ≠ address := by
      intro hh
      subst address
      exact safe value (by simp [he])
    rw [hm,update_other _ _ _ _ ha]

/-- The source memory-frame rule follows the complete application trace across
sequences, loops, early returns, recursive calls, and exhaustion. -/
theorem Evaluation.frame {w free : Nat} {p : Program} {rho : RandomMemory w} {stmt : Stmt}
    {locals : Locals w} {mem mem' : DataMemory w} {flow : Flow w} {trace : List (Access w)}
    (d : Evaluation p rho free stmt locals mem flow mem' trace) (protectedCell : Addr w)
    (safe : ∀ value, .dataWrite protectedCell value ∉ trace) :
    mem' protectedCell = mem protectedCell := by
  induction d with
  | skip | whileFalse | callExhausts | ret => rfl
  | primitive h => exact Primitive.frame h safe
  | sequence a b ia ib | whileContinue _ a b ia ib =>
    have ha := ia (fun value h => safe value (List.mem_append.mpr (.inl h)))
    have hb := ib (fun value h => safe value (List.mem_append.mpr (.inr h)))
    exact hb.trans ha
  | sequenceStop _ _ ih | ifTrue _ _ ih | ifFalse _ _ ih | whileStop _ _ _ ih => exact ih safe
  | call _ _ _ _ _ _ ih | callBodyExhausts _ _ _ _ _ _ ih => exact ih safe

/-- An application access policy gives preservation of every forbidden write
cell, independently of the compiler and independently of allowed reads. -/
theorem Evaluation.frame_of_policy {w free : Nat} {p : Program} {rho : RandomMemory w} {stmt : Stmt}
    {locals : Locals w} {mem mem' : DataMemory w} {flow : Flow w} {trace : List (Access w)}
    (d : Evaluation p rho free stmt locals mem flow mem' trace) {policy : AccessPolicy w}
    (hp : policy.AllowsTrace trace) {address : Addr w} (ha : ¬policy.write address) :
    mem' address = mem address :=
  d.frame address (fun value he => ha (hp (.dataWrite address value) he))

end RamLang
