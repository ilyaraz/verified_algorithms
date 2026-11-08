import DataStructures.PerfectHash.Build.Model

namespace PerfectHash.Build
open FiniteProbability

/-- Stage states retain completed children. A stage invokes the explicit finite
retry/fallback search; its work is charged per tested candidate in Build.Bounds. -/
inductive Phase (Seed : Type) (m : Nat) where
  | root
  | children (rootSeed : Seed) (next : Nat) (built : Fin m → Option (ChildChoice Seed))
  | done (dictionary : Dictionary Seed m)
  | failed

variable {Key Seed : Type} {m : Nat} {xs : List Key}

def Model.advance (model : Model Key Seed m xs)
    (rootSamples : Fin model.attempts → Seed) (childSamples : Fin m → Fin model.attempts → Seed) :
    Phase Seed m → Phase Seed m
  | .root => match model.rootSearch rootSamples with
      | none => .failed
      | some a => .children a 0 (fun _ => none)
  | .children a next built =>
      if hn : next < m then
        match model.childSearch a ⟨next,hn⟩ (childSamples ⟨next,hn⟩) with
        | none => .failed
        | some c => .children a (next+1) (fun b => if b.val = next then some c else built b)
      else match sequenceFin built with
        | none => .failed
        | some children => .done ⟨a,children⟩
  | .done dict => .done dict
  | .failed => .failed

def Model.advanceMany (model : Model Key Seed m xs)
    (rootSamples : Fin model.attempts → Seed) (childSamples : Fin m → Fin model.attempts → Seed) :
    Nat → Phase Seed m → Phase Seed m
  | 0,s => s
  | n+1,s => model.advanceMany rootSamples childSamples n (model.advance rootSamples childSamples s)

@[simp] theorem advance_done (model : Model Key Seed m xs) (rootSamples childSamples) (dict : Dictionary Seed m) :
    model.advance rootSamples childSamples (.done dict) = .done dict := rfl

@[simp] theorem advanceMany_done (model : Model Key Seed m xs) (rootSamples childSamples)
    (n : Nat) (dict : Dictionary Seed m) :
    model.advanceMany rootSamples childSamples n (.done dict) = .done dict := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [Model.advanceMany] using ih

variable [DecidableEq Key] [Fintype Seed] [Nonempty Seed]

/-- Each child stage extends the initialized prefix by exactly one valid child;
successful siblings survive every retry in the current child's search. -/
theorem finish_children (model : Model Key Seed m xs) (hyp : Hypotheses model)
    (rootSamples : Fin model.attempts → Seed) (childSamples : Fin m → Fin model.attempts → Seed)
    {a : Seed} (ha : rootAccept model.root xs a = true)
    (r next : Nat) (hn : next+r = m) (built : Fin m → Option (ChildChoice Seed))
    (hb : ∀ b, b.val < next → built b = model.childSearch a b (childSamples b)) :
    ∃ dict, model.advanceMany rootSamples childSamples (r+1) (.children a next built) = .done dict ∧
      dict.root = a ∧ model.Valid dict ∧
      ∀ b, model.childSearch a b (childSamples b) = some (dict.children b) := by
  induction r generalizing next built with
  | zero =>
    have hn' : next = m := by omega
    have hcorrect (b : Fin m) : built b = model.childSearch a b (childSamples b) :=
      hb b (by rw [hn']; exact b.isLt)
    have hex (b : Fin m) : ∃ c, built b = some c := by
      obtain ⟨c,hc,_⟩ := child_search_total model hyp ha b (childSamples b)
      exact ⟨c,(hcorrect b).trans hc⟩
    obtain ⟨cs,hcs,hvalues⟩ := sequenceFin_total built hex
    refine ⟨⟨a,cs⟩,?_,rfl,⟨ha,?_⟩,?_⟩
    · simp [Model.advanceMany,Model.advance,hn',hcs]
    · intro b
      obtain ⟨c,hc,hvalid⟩ := child_search_total model hyp ha b (childSamples b)
      have he : cs b = c := Option.some.inj ((hvalues b).symm.trans ((hcorrect b).trans hc))
      simpa [he] using hvalid
    · intro b
      exact (hcorrect b).symm.trans (hvalues b)
  | succ r ih =>
    have hn' : next < m := by omega
    let b : Fin m := ⟨next,hn'⟩
    obtain ⟨c,hc,hvalid⟩ := child_search_total model hyp ha b (childSamples b)
    let built' : Fin m → Option (ChildChoice Seed) := fun i => if i.val = next then some c else built i
    have hb' : ∀ i, i.val < next+1 → built' i = model.childSearch a i (childSamples i) := by
      intro i hi
      by_cases he : i.val = next
      · have hi' : i = b := Fin.ext he
        subst i
        simpa [built',b] using hc.symm
      · simpa [built',he] using hb i (by omega)
    obtain ⟨dict,hd,hroot,hgood,hchildren⟩ := ih (next+1) (by omega) built' hb'
    refine ⟨dict,?_,hroot,hgood,hchildren⟩
    change model.childSearch a ⟨next,hn'⟩ (childSamples ⟨next,hn'⟩) = some c at hc
    change model.advanceMany rootSamples childSamples (r+1)
      (model.advance rootSamples childSamples (.children a next built)) = _
    rw [Model.advance,dif_pos hn',hc]
    exact hd

/-- All admissible abstract executions complete in a fixed number of stages;
additional stages preserve the completed dictionary. Trial work is counted
separately and includes the complete capped-random and exhaustive searches. -/
theorem advanceMany_total (model : Model Key Seed m xs) (hyp : Hypotheses model)
    (rootSamples : Fin model.attempts → Seed) (childSamples : Fin m → Fin model.attempts → Seed) :
    ∃ dict, model.advanceMany rootSamples childSamples (m+2) .root = .done dict ∧ model.Valid dict := by
  obtain ⟨a,ha,hgood⟩ := root_search_total model hyp rootSamples
  obtain ⟨dict,hd,_,hvalid,_⟩ := finish_children model hyp rootSamples childSamples hgood m 0
    (by omega) (fun _ => none) (by intro b hb; omega)
  refine ⟨dict,?_,hvalid⟩
  simpa only [Model.advanceMany,Model.advance,ha] using hd

end PerfectHash.Build
