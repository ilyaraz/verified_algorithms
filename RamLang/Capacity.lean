import RamLang.EvaluationSoundness

namespace RamLang
open WordRam

variable {w cap n : Nat} {p : Program} {rho : RandomMemory w} {s t : Config w}
  {event : Option (Access w)} {log : List (Access w)} {value : Word w}

/-- Any continuing capacity-aware step is also an ideal source step. The finite
semantics adds only allocation failure; it does not change successful actions. -/
theorem Step.forgetCapacity (hs : Step p rho (some cap) s t event) : Step p rho none s t event := by
  cases hc : s.control with
  | run a => simpa only [Step,step,hc] using hs
  | enter id args =>
    simp only [Step,step,hc,enter] at hs ⊢
    cases hf : p.functions[id]? with
    | none => simp [hf] at hs
    | some f =>
      simp only [hf] at hs ⊢
      split at hs
      · cases hs
      · rename_i ha
        split at hs
        · simpa only [ha,↓reduceIte,Option.all_none] using hs
        · cases hs

/-- Successful finite source prefixes forget capacity without losing their effects. -/
theorem Steps.forgetCapacity (hs : Steps p rho (some cap) n s t log) : Steps p rho none n s t log := by
  induction hs with
  | refl => exact .refl _
  | cons h tail ih => exact .cons h.forgetCapacity ih

/-- Runtime returns agree with ideal semantics; stack exhaustion remains a
separate finite-capacity outcome and is intentionally not mapped to a return. -/
theorem Returns.forgetCapacity (hs : Returns p rho (some cap) s value t log) :
    Returns p rho none s value t log := by
  obtain ⟨n,hsteps,hret⟩ := hs
  refine ⟨n,hsteps.forgetCapacity,?_⟩
  cases hc : t.control with
  | run a => simpa only [step,hc] using hret
  | enter id args =>
    simp only [step,hc,enter] at hret
    cases hf : p.functions[id]? with
    | none => simp [hf] at hret
    | some f =>
      simp only [hf] at hret
      split at hret
      · cases hret
      · split at hret <;> cases hret

/-- A source proof with a sufficient finite stack establishes the ideal behavior too. -/
theorem Evaluation.ideal_returns {free function : Nat} {stmt : Stmt} {locals : Locals w}
    {mem mem' : DataMemory w}
    (d : Evaluation p rho free stmt locals mem (.returned value) mem' log) :
    ∃ c, Returns p rho none (atStatement function locals [stmt] [] mem) value c log ∧ c.mem = mem' := by
  obtain ⟨c,hs,hm⟩ := d.returns (cap := free+2+locals.length) (function := function) rfl
  exact ⟨c,hs.forgetCapacity,hm⟩

end RamLang
