import DataStructures.PerfectHash.Build.Model

namespace PerfectHash.Build
open Buckets

variable {Key Seed : Type} {m : Nat} {xs : List Key}

/-- Abstract slot coordinates. Direct buckets use slot zero; nontrivial buckets
use the accepted child seed. Physical address encoding is a later refinement. -/
def Model.position (model : Model Key Seed m xs) (dict : Dictionary Seed m) (x : Key) : Fin m × Nat :=
  let b := model.root.eval dict.root x
  (b,match dict.children b with
      | .direct => 0
      | .hashed seed => ((model.child dict.root b).eval seed x).val)

/-- The conceptual stored-key table is derived constructively from placement.
This is a mathematical table, not a constant-cost RAM lookup implementation. -/
def Model.stored (model : Model Key Seed m xs) (dict : Dictionary Seed m) (p : Fin m × Nat) : Option Key :=
  xs.find? (fun x => model.position dict x == p)

variable [DecidableEq Key]

theorem short_list_unique {ys : List Key} (hl : ys.length ≤ 1) {x y : Key}
    (hx : x ∈ ys) (hy : y ∈ ys) : x = y := by
  cases ys with
  | nil => simp at hx
  | cons a ys =>
    have hn : ys = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hl; omega)
    simp [hn] at hx hy
    exact hx.trans hy.symm

/-- Every valid abstract dictionary is injective on its distinct input keys. -/
theorem position_injective (model : Model Key Seed m xs) (hx : xs.Nodup)
    {dict : Dictionary Seed m} (hd : model.Valid dict) :
    Set.InjOn (model.position dict) {x | x ∈ xs} := by
  intro x hxm y hym he
  change x ∈ xs at hxm
  change y ∈ xs at hym
  have hb : model.root.eval dict.root x = model.root.eval dict.root y := congrArg Prod.fst he
  let b := model.root.eval dict.root x
  have hxb : x ∈ model.childKeys dict.root b := by simp [Model.childKeys,b,hxm]
  have hyb : y ∈ model.childKeys dict.root b := by simp [Model.childKeys,b,hym,hb]
  have hc := hd.2 b
  cases hcdef : dict.children b with
  | direct =>
    simp only [Model.ChildValid,hcdef] at hc
    exact short_list_unique hc hxb hyb
  | hashed seed =>
    simp only [Model.ChildValid,hcdef,childAccept,decide_eq_true_eq] at hc
    have hinj := (pairs_zero_iff ((model.child dict.root b).eval seed)
      (model.childKeys dict.root b) (nodup _ _ _ hx)).mp hc
    have hi : ((model.child dict.root b).eval seed x).val = ((model.child dict.root b).eval seed y).val := by
      have hh := congrArg Prod.snd he
      dsimp only [Model.position] at hh
      rw [← hb] at hh
      change (match dict.children b with | .direct => 0 | .hashed a => ((model.child dict.root b).eval a x).val) =
        (match dict.children b with | .direct => 0 | .hashed a => ((model.child dict.root b).eval a y).val) at hh
      simpa only [hcdef] using hh
    exact hinj hxb hyb (Fin.ext hi)

/-- Each member is stored under its unique coordinate, with the full key value. -/
theorem stored_member (model : Model Key Seed m xs) (hx : xs.Nodup)
    {dict : Dictionary Seed m} (hd : model.Valid dict) {x : Key} (hxm : x ∈ xs) :
    model.stored dict (model.position dict x) = some x := by
  have hinj := position_injective model hx hd
  cases he : model.stored dict (model.position dict x) with
  | none =>
    have hh := List.find?_eq_none.mp he x hxm
    simp at hh
  | some y =>
    have hy := List.mem_of_find?_eq_some he
    have hpos : model.position dict y = model.position dict x := by
      simpa using List.find?_some he
    have hyx := hinj hy hxm hpos
    simp [hyx]

/-- Comparing the stored full key rejects nonmembers even when their coordinates
collide with an occupied slot. -/
theorem stored_membership (model : Model Key Seed m xs) (hx : xs.Nodup)
    {dict : Dictionary Seed m} (hd : model.Valid dict) (q : Key) :
    model.stored dict (model.position dict q) = some q ↔ q ∈ xs := by
  constructor
  · exact List.mem_of_find?_eq_some
  · exact stored_member model hx hd

end PerfectHash.Build
