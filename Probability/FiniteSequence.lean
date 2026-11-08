import Probability.FiniteSearch

namespace FiniteProbability

/-- A homogeneous finite-function constructor with no proof-axiom dependencies. -/
def consFin {α : Type*} {n : Nat} (head : α) (tail : Fin n → α) : Fin (n+1) → α
  | ⟨0,_⟩ => head
  | ⟨k+1,h⟩ => tail ⟨k,Nat.lt_of_succ_lt_succ h⟩

/-- Sequence finitely many optional results without choosing witnesses from proofs. -/
def sequenceFin {α : Type*} : {n : Nat} → (Fin n → Option α) → Option (Fin n → α)
  | 0,_ => some (fun i => Fin.elim0 i)
  | n+1,f => do
      let head ← f ⟨0,Nat.zero_lt_succ n⟩
      let tail ← sequenceFin (fun i => f i.succ)
      pure (consFin head tail)

theorem sequenceFin_total {α : Type*} {n : Nat} (f : Fin n → Option α)
    (hf : ∀ i, ∃ a, f i = some a) :
    ∃ g, sequenceFin f = some g ∧ ∀ i, f i = some (g i) := by
  induction n with
  | zero => exact ⟨fun i => Fin.elim0 i,rfl,fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨a,ha⟩ := hf ⟨0,Nat.zero_lt_succ n⟩
    obtain ⟨g,hg,hvalues⟩ := ih (fun i => f i.succ) (fun i => hf i.succ)
    refine ⟨consFin a g,?_,?_⟩
    · simp only [sequenceFin,ha,hg]
      rfl
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [consFin] using ha
      · simpa [consFin] using hvalues j

end FiniteProbability
