import WordRam.Word

namespace WordRam

abbrev DataMemory (w : Nat) := Addr w → Word w
abbrev RandomMemory (w : Nat) := Addr w → Word w

def update [DecidableEq α] (f : α → β) (a : α) (v : β) : α → β :=
  fun b => if b = a then v else f b

@[simp] theorem update_same [DecidableEq α] (f : α → β) (a : α) (v : β) :
    update f a v a = v := by simp [update]

@[simp] theorem update_other [DecidableEq α] (f : α → β) (a b : α) (v : β)
    (h : b ≠ a) : update f a v b = f b := by simp [update, h]

theorem update_shadow [DecidableEq α] (f : α → β) (a : α) (v u : β) :
    update (update f a v) a u = update f a u := by
  funext b
  by_cases h : b = a <;> simp [update, h]

theorem update_comm [DecidableEq α] (f : α → β) (a b : α) (v u : β)
    (h : a ≠ b) : update (update f a v) b u = update (update f b u) a v := by
  funext c
  by_cases ha : c = a <;> by_cases hb : c = b <;> simp_all [update]

def zeroMemory (w : Nat) : DataMemory w := fun _ => 0

end WordRam
