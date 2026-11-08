import WordRam.Memory

/-! Natural address intervals and array assertions, independent of algorithms. -/
namespace WordRam

structure Region where
  base : Nat
  size : Nat
  deriving DecidableEq, Repr

def Region.Fits (r : Region) (w : Nat) : Prop := r.base + r.size < modulus w

def Region.Contains (r : Region) (a : Addr w) : Prop :=
  r.base ≤ a.toNat ∧ a.toNat < r.base + r.size

def Region.Separated (r s : Region) : Prop :=
  r.base + r.size ≤ s.base ∨ s.base + s.size ≤ r.base

def AgreeOn (r : Region) (mem mem' : DataMemory w) : Prop :=
  ∀ a, r.Contains a → mem a = mem' a

def ArrayAt (mem : DataMemory w) (base : Nat) (xs : List (Word w)) : Prop :=
  ∀ i : Fin xs.length, mem (word w (base + i.val)) = xs[i]

variable {w : Nat} {r s : Region} {i base : Nat} {a : Addr w}
  {mem mem' : DataMemory w} {xs : List (Word w)} {x v : Word w}

theorem Region.index_lt (h : r.Fits w) (hi : i ≤ r.size) :
    r.base + i < modulus w := by
  unfold Fits at h
  omega

theorem Region.contains_index (h : r.Fits w) (hi : i < r.size) :
    r.Contains (word w (r.base + i)) := by
  unfold Contains
  rw [word_toNat_of_lt (Region.index_lt h (Nat.le_of_lt hi))]
  omega

theorem Region.not_contains_of_separated (h : r.Separated s)
    (ha : r.Contains a) : ¬ s.Contains a := by
  unfold Separated at h
  unfold Contains at *
  rcases h with h | h <;> omega

theorem Region.separated_symm (h : r.Separated s) : s.Separated r := h.symm

theorem AgreeOn.refl (r : Region) (mem : DataMemory w) : AgreeOn r mem mem :=
  fun _ _ => rfl

theorem AgreeOn.symm (h : AgreeOn r mem mem') : AgreeOn r mem' mem :=
  fun a ha => (h a ha).symm

theorem AgreeOn.trans {m₁ m₂ m₃ : DataMemory w}
    (h : AgreeOn r m₁ m₂) (g : AgreeOn r m₂ m₃) : AgreeOn r m₁ m₃ :=
  fun x hx => (h x hx).trans (g x hx)

theorem ArrayAt.congr (h : ArrayAt mem base xs)
    (hf : (Region.mk base xs.length).Fits w)
    (ha : AgreeOn ⟨base, xs.length⟩ mem mem') : ArrayAt mem' base xs := by
  intro i
  rw [← ha _ (Region.contains_index hf i.isLt)]
  exact h i

@[simp] theorem arrayAt_nil (mem : DataMemory w) (base : Nat) : ArrayAt mem base [] := by
  intro i
  exact Fin.elim0 i

theorem arrayAt_cons : ArrayAt mem base (x :: xs) ↔
    mem (word w base) = x ∧ ArrayAt mem (base + 1) xs := by
  constructor
  · intro h
    constructor
    · simpa using h ⟨0, by simp⟩
    · intro i
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        h ⟨i.val + 1, by simp⟩
  · rintro ⟨hx, hs⟩ ⟨i, hi⟩
    cases i with
    | zero => simpa using hx
    | succ i =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        hs ⟨i, by simpa using hi⟩

theorem ArrayAt.update_outside (h : ArrayAt mem base xs)
    (hf : (Region.mk base xs.length).Fits w)
    (ha : ¬ (Region.mk base xs.length).Contains a) :
    ArrayAt (update mem a v) base xs := by
  intro i
  rw [update_other]
  · exact h i
  · intro he
    exact ha (he ▸ Region.contains_index hf i.isLt)

theorem word_eq_iff_of_lt {a b : Nat} (ha : a < modulus w) (hb : b < modulus w) :
    word w a = word w b ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simpa [word_toNat_of_lt ha, word_toNat_of_lt hb] using this
  · rintro rfl
    rfl

theorem arrayAt_append (mem : DataMemory w) (base : Nat) (xs ys : List (Word w)) :
    ArrayAt mem base (xs++ys) ↔ ArrayAt mem base xs ∧ ArrayAt mem (base+xs.length) ys := by
  induction xs generalizing base with
  | nil => simp
  | cons x xs ih =>
    simp only [List.cons_append, arrayAt_cons, ih, List.length_cons, and_assoc]
    have he : base + 1 + xs.length = base + (xs.length+1) := by omega
    rw [he]

theorem AgreeOn.update_outside (h : AgreeOn r mem mem') (ha : ¬ r.Contains a) :
    AgreeOn r mem (update mem' a v) := by
  intro b hb
  rw [update_other]
  · exact h b hb
  · intro he
    exact ha (he ▸ hb)

theorem ArrayAt.push (h : ArrayAt mem base xs) (hf : base+xs.length+1 < modulus w) :
    ArrayAt (update mem (word w (base+xs.length)) v) base (xs++[v]) := by
  rw [arrayAt_append]
  constructor
  · apply h.update_outside (by unfold Region.Fits; simp only; omega)
    unfold Region.Contains
    rw [word_toNat_of_lt (by omega : base+xs.length < modulus w)]
    simp
  · rw [arrayAt_cons]
    exact ⟨update_same _ _ _, by simp⟩

theorem update_word (mem : DataMemory w) (v : Word w) (a : Addr w)
    (hf : n < modulus w) :
    update mem (word w n) v a = if a.toNat = n then v else mem a := by
  have he : a = word w n ↔ a.toNat = n := by
    constructor
    · rintro rfl
      exact word_toNat_of_lt hf
    · intro h
      apply BitVec.eq_of_toNat_eq
      rw [h, word_toNat_of_lt hf]
  simp only [update, he]

theorem word_add (a b : Nat) : word w a + word w b = word w (a+b) :=
  BitVec.ofNat_add_ofNat a b

theorem word_mul (a b : Nat) : word w a * word w b = word w (a*b) :=
  BitVec.ofNat_mul_ofNat a b

theorem word_sub (a b : Nat) (hb : b < modulus w) (hba : b ≤ a) :
    word w a - word w b = word w (a-b) :=
  BitVec.ofNat_sub_ofNat_of_le a b hb hba

end WordRam
