import RamLang.Semantics
import RamLang.Compiler.Proofs.Code

namespace RamLang.Compiler
open WordRam

/-- Word literals commute with modular addition, whether or not the sum wraps. -/
theorem word_add (a b : Nat) : word w a + word w b = word w (a+b) :=
  (BitVec.ofNat_add a b).symm

def slotAddress (base id : Nat) : Addr w := word w (base+2+id)

theorem slotAddress_eq (base id : Nat) :
    word w base + word w (2+id) = (slotAddress base id : Addr w) := by
  rw [word_add]
  simp [slotAddress, Nat.add_assoc]

/-- The one-past-frame address is representable, as required by the stack ABI. -/
def FrameFits (w base slots : Nat) : Prop := base + 2 + slots < modulus w

/-- Uninitialized slots impose no condition on dirty physical stack memory. -/
def FrameLocals (mem : DataMemory w) (base : Nat) (locals : Locals w) : Prop :=
  ∀ i v, locals[i]? = some (some v) → mem (slotAddress base i) = v

variable {w base count dst i j : Nat} {mem : DataMemory w}
  {locals result : Locals w} {a : Addr w} {value : Word w} {args : List (Word w)}

theorem FrameFits.slot_lt (h : FrameFits w base count) (hi : i < count) :
    base+2+i < modulus w := by unfold FrameFits at h; omega

theorem FrameFits.slot_ne (h : FrameFits w base count) (hi : i < count) (hj : j < count)
    (hne : i ≠ j) : (slotAddress base i : Addr w) ≠ slotAddress base j := by
  intro he
  have hh := (word_eq_iff_of_lt (h.slot_lt hi) (h.slot_lt hj)).mp he
  omega

/-- Spilling one local changes exactly that local's assertion. -/
theorem FrameLocals.set (h : FrameLocals mem base locals) (hf : FrameFits w base locals.length)
    (hd : dst < locals.length) (value : Word w) :
    FrameLocals (update mem (slotAddress base dst) value) base (locals.set dst (some value)) := by
  intro i v hi
  by_cases he : dst = i
  · subst i
    simp only [List.getElem?_set_self hd, Option.some.injEq] at hi
    cases hi
    exact update_same _ _ _
  · rw [List.getElem?_set, if_neg he] at hi
    have hb : i < locals.length := (List.getElem?_eq_some_iff.mp hi).1
    rw [update_other _ _ _ _ (hf.slot_ne hb hd (Ne.symm he))]
    exact h i v hi

/-- A write outside the frame leaves every initialized local available. -/
theorem FrameLocals.update_outside (h : FrameLocals mem base locals)
    (ha : ∀ i, i < locals.length → a ≠ (slotAddress base i : Addr w)) (value : Word w) :
    FrameLocals (update mem a value) base locals := by
  intro i v hi
  rw [update_other _ _ _ _ (Ne.symm (ha i (List.getElem?_eq_some_iff.mp hi).1))]
  exact h i v hi

/-- Successful local updates preserve the invocation's fixed slot count. -/
theorem writeLocal_length (h : writeLocal locals dst value = .ok result) :
    result.length = locals.length := by
  unfold writeLocal at h
  split at h
  · cases h
    exact List.length_set
  · cases h

/-- Initialized parameters suffice to represent an activation with dirty locals. -/
theorem FrameLocals.parameters (h : ArrayAt mem (base+2) args) (count : Nat) :
    FrameLocals mem base (args.map some ++ List.replicate count none) := by
  intro i v hi
  by_cases hb : i < args.length
  · rw [List.getElem?_append_left (by simpa)] at hi
    simp only [List.getElem?_map, List.getElem?_eq_getElem hb, Option.map_some,
      Option.some.injEq] at hi
    simpa [slotAddress, hi] using h ⟨i, hb⟩
  · rw [List.getElem?_append_right (by simp; omega)] at hi
    simp only [List.length_map, List.getElem?_replicate] at hi
    split at hi <;> cases hi

end RamLang.Compiler
