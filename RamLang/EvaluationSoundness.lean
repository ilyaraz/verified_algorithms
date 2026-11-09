import RamLang.Evaluation

namespace RamLang
open WordRam

/-- Source configuration at a statement boundary with an arbitrary continuation. -/
def atStatement (function : FunctionId) (locals : Locals w) (todo : List Stmt)
    (callers : List (Caller w)) (mem : DataMemory w) : Config w :=
  ⟨.run ⟨function,locals,todo⟩,callers,mem⟩

/-- A structured return stops just before its operational return transition.
That transition either resumes a caller or reports the outermost return. -/
def AtReturn (function : FunctionId) (callers : List (Caller w)) (slots : Nat)
    (value : Word w) (mem : DataMemory w) (c : Config w) : Prop :=
  ∃ locals atom rest, c = atStatement function locals (.ret atom::rest) callers mem ∧
    locals.length = slots ∧ atom.eval locals = .ok value

/-- Finite structured outcomes viewed in the independent small-step semantics. -/
def SourcePost (p : Program) (rho : RandomMemory w) (cap : Nat)
    (function : FunctionId) (rest : List Stmt) (callers : List (Caller w)) (slots : Nat)
    (flow : Flow w) (mem : DataMemory w) (c : Config w) : Prop :=
  match flow with
  | .next locals => c = atStatement function locals rest callers mem
  | .returned v => AtReturn function callers slots v mem c
  | .exhausted => c.mem = mem ∧ step p rho (some cap) c = .stop .stackExhausted

variable {w cap free function slots : Nat} {p : Program} {rho : RandomMemory w}
  {locals : Locals w} {mem mem' : DataMemory w} {flow : Flow w} {stmt : Stmt}
  {rest : List Stmt} {callers : List (Caller w)} {log : List (Access w)} {c : Config w}

theorem SourcePost.changeTodo (h : SourcePost p rho cap function rest callers slots flow mem c)
    (hs : flow.stops) (other : List Stmt) :
    SourcePost p rho cap function other callers slots flow mem c := by
  cases flow with
  | next _ => exact False.elim hs
  | returned _ => exact h
  | exhausted => exact h

/-- Every finite derivation is a genuine finite execution of the independent
source machine, retaining arbitrary surrounding continuations and caller stacks. -/
theorem Evaluation.sound (d : Evaluation p rho free stmt locals mem flow mem' log)
    (hcap : cap = free + 2 + locals.length + (callers.map (fun c => 2+c.activation.locals.length)).sum) :
    ∃ n c, Steps p rho (some cap) n (atStatement function locals (stmt::rest) callers mem) c log ∧
      SourcePost p rho cap function rest callers locals.length flow mem' c := by
  induction d generalizing function rest callers with
  | @skip free locals mem =>
    refine ⟨1,atStatement function locals rest callers mem,?_,rfl⟩
    refine Steps.cons (event := none) ?_ (.refl _)
    rfl
  | @primitive free op locals mem locals' mem' event he =>
    refine ⟨1,atStatement function locals' rest callers mem',?_,rfl⟩
    have hs : Step p rho (some cap) (atStatement function locals (.primitive op::rest) callers mem)
        (atStatement function locals' rest callers mem') event := by simp [Step,step,atStatement,he]
    simpa using Steps.cons hs (.refl _)
  | @sequence free a locals mem middle mem₁ trace₁ b flow mem₂ trace₂ first second ia ib =>
    obtain ⟨n,c,hs,hp⟩ := ia (function := function) (rest := b::rest) (callers := callers) hcap
    change c = atStatement function middle (b::rest) callers mem₁ at hp
    subst c
    have hlen := first.preserves_length
    obtain ⟨m,u,ht,hq⟩ := ib (function := function) (rest := rest) (callers := callers) (by simpa only [hlen] using hcap)
    refine ⟨n+m+1,u,?_,?_⟩
    · refine Steps.cons (event := none) ?_ (hs.trans ht)
      rfl
    · simpa only [hlen] using hq
  | @sequenceStop free a locals mem flow mem' trace b first stop ih =>
    obtain ⟨n,c,hs,hp⟩ := ih (function := function) (rest := b::rest) (callers := callers) hcap
    refine ⟨n+1,c,?_,hp.changeTodo stop _⟩
    refine Steps.cons (event := none) ?_ hs
    rfl
  | @ifTrue free yes locals mem flow mem' trace condition no test branch ih =>
    obtain ⟨n,c,hs,hp⟩ := ih (function := function) (rest := rest) (callers := callers) hcap
    refine ⟨n+1,c,?_,hp⟩
    refine Steps.cons (event := none) ?_ hs
    simp [Step,step,atStatement,test]
  | @ifFalse free no locals mem flow mem' trace condition yes test branch ih =>
    obtain ⟨n,c,hs,hp⟩ := ih (function := function) (rest := rest) (callers := callers) hcap
    refine ⟨n+1,c,?_,hp⟩
    refine Steps.cons (event := none) ?_ hs
    simp [Step,step,atStatement,test]
  | @whileFalse free condition body locals mem test =>
    refine ⟨1,atStatement function locals rest callers mem,?_,rfl⟩
    refine Steps.cons (event := none) ?_ (.refl _)
    simp [Step,step,atStatement,test]
  | @whileContinue free body locals mem middle mem₁ trace₁ condition flow mem₂ trace₂ test iteration tail ia ib =>
    obtain ⟨n,c,hs,hp⟩ := ia (function := function) (rest := .while condition body::rest) (callers := callers) hcap
    change c = atStatement function middle (.while condition body::rest) callers mem₁ at hp
    subst c
    have hlen := iteration.preserves_length
    obtain ⟨m,u,ht,hq⟩ := ib (function := function) (rest := rest) (callers := callers) (by simpa only [hlen] using hcap)
    refine ⟨n+m+1,u,?_,?_⟩
    · refine Steps.cons (event := none) ?_ (hs.trans ht)
      simp [Step,step,atStatement,test]
    · simpa only [hlen] using hq
  | @whileStop free body locals mem flow mem' trace condition test iteration stop ih =>
    obtain ⟨n,c,hs,hp⟩ := ih (function := function) (rest := .while condition body::rest) (callers := callers) hcap
    refine ⟨n+1,c,?_,hp.changeTodo stop _⟩
    refine Steps.cons (event := none) ?_ hs
    simp [Step,step,atStatement,test]
  | @call callee f free mem v mem' trace locals dst locals' args values lookup arguments arity space body assign ih =>
    let suspended : Caller w := ⟨⟨function,locals,rest⟩,dst⟩
    let entering : Config w := ⟨.enter callee values,suspended::callers,mem⟩
    let initial := atStatement callee (values.map some ++ List.replicate f.locals.length none) [f.body]
      (suspended::callers) mem
    have hlen : (values.map some ++ List.replicate f.locals.length (none : Option (Word w))).length = f.slots := by
      simp [Function.slots,arity]
    have hcap' : cap = (free-f.frameSize)+2+f.slots+
        ((suspended::callers).map (fun c => 2+c.activation.locals.length)).sum := by
      simp only [List.map_cons,List.sum_cons,suspended] at *
      unfold Function.frameSize at space ⊢
      omega
    obtain ⟨n,c,hs,hp⟩ := ih (function := callee) (rest := []) (callers := suspended::callers) (by
      rw [hlen]; exact hcap')
    obtain ⟨out,atom,todo,hc,_,hv⟩ := hp
    subst c
    have hcall : Step p rho (some cap) (atStatement function locals (.call dst callee args::rest) callers mem) entering none := by
      simp [Step,step,atStatement,entering,suspended,(writeLocal_ok assign).1,arguments]
    have henter : Step p rho (some cap) entering initial none := by
      have hf : 2+locals.length+(callers.map (fun c => 2+c.activation.locals.length)).sum+f.frameSize ≤ cap := by omega
      simpa [Step,step,enter,entering,initial,atStatement,lookup,arity,Config.stackWords,suspended,
        List.map_cons,List.sum_cons,Nat.add_assoc] using hf
    have hreturn : Step p rho (some cap) (atStatement callee out (.ret atom::todo) (suspended::callers) mem')
        (atStatement function locals' rest callers mem') none := by
      simp [Step,step,atStatement,suspended,hv,assign]
    refine ⟨(n+1)+1+1,_,.cons hcall (.cons henter ?_),rfl⟩
    simpa using hs.trans (.cons hreturn (.refl _))
  | @callExhausts callee f dst free args locals mem values lookup arguments arity destination space =>
    let suspended : Caller w := ⟨⟨function,locals,rest⟩,dst⟩
    let entering : Config w := ⟨.enter callee values,suspended::callers,mem⟩
    have hcall : Step p rho (some cap) (atStatement function locals (.call dst callee args::rest) callers mem) entering none := by
      simp [Step,step,atStatement,entering,suspended,destination,arguments]
    refine ⟨1,entering,.cons hcall (.refl _),rfl,?_⟩
    have hf : ¬ (2+locals.length+(callers.map (fun c => 2+c.activation.locals.length)).sum+f.frameSize ≤ cap) := by omega
    simp [step,enter,entering,lookup,arity,Config.stackWords,suspended,Nat.add_assoc] at hf ⊢
    exact hf
  | @callBodyExhausts callee f dst free mem mem' trace args locals values lookup arguments arity destination space body ih =>
    let suspended : Caller w := ⟨⟨function,locals,rest⟩,dst⟩
    let entering : Config w := ⟨.enter callee values,suspended::callers,mem⟩
    let initial := atStatement callee (values.map some ++ List.replicate f.locals.length none) [f.body]
      (suspended::callers) mem
    have hlen : (values.map some ++ List.replicate f.locals.length (none : Option (Word w))).length = f.slots := by
      simp [Function.slots,arity]
    have hcap' : cap = (free-f.frameSize)+2+f.slots+
        ((suspended::callers).map (fun c => 2+c.activation.locals.length)).sum := by
      simp only [List.map_cons,List.sum_cons,suspended] at *
      unfold Function.frameSize at space ⊢
      omega
    obtain ⟨n,c,hs,hp⟩ := ih (function := callee) (rest := []) (callers := suspended::callers) (by
      rw [hlen]; exact hcap')
    have hcall : Step p rho (some cap) (atStatement function locals (.call dst callee args::rest) callers mem) entering none := by
      simp [Step,step,atStatement,entering,suspended,destination,arguments]
    have henter : Step p rho (some cap) entering initial none := by
      have hf : 2+locals.length+(callers.map (fun c => 2+c.activation.locals.length)).sum+f.frameSize ≤ cap := by omega
      simpa [Step,step,enter,entering,initial,atStatement,lookup,arity,Config.stackWords,suspended,
        List.map_cons,List.sum_cons,Nat.add_assoc] using hf
    exact ⟨n+1+1,c,.cons hcall (.cons henter hs),hp⟩
  | @ret free atom locals mem v hx =>
    exact ⟨0,_,.refl _,locals,atom,rest,rfl,rfl,hx⟩

/-- A structured return from an outermost invocation is an operational return
with exactly the same application memory and ordered access trace. -/
theorem Evaluation.returns {value : Word w}
    (d : Evaluation p rho free stmt locals mem (.returned value) mem' log)
    (hcap : cap = free+2+locals.length) :
    ∃ c, Returns p rho (some cap) (atStatement function locals [stmt] [] mem) value c log ∧ c.mem = mem' := by
  obtain ⟨n,c,hs,hp⟩ := d.sound (function := function) (rest := []) (callers := []) (by simpa using hcap)
  obtain ⟨out,atom,todo,hc,_,hv⟩ := hp
  subst c
  refine ⟨_,⟨n,hs,?_⟩,rfl⟩
  simp [step,atStatement,hv]

/-- Entering a fitting top-level function and its structured body yields the
independent source interpreter's successful return, without compiler premises. -/
theorem Evaluation.invocationReturns {callee : FunctionId} {f : Function}
    {values : List (Word w)} {value : Word w}
    (lookup : p.functions[callee]? = some f) (arity : values.length = f.parameters.length)
    (space : f.frameSize ≤ cap)
    (d : Evaluation p rho (cap-f.frameSize) f.body
      (values.map some ++ List.replicate f.locals.length none) mem (.returned value) mem' log) :
    ∃ c, Returns p rho (some cap) ⟨.enter callee values,[],mem⟩ value c log ∧ c.mem = mem' := by
  have hcap : cap = cap-f.frameSize+2+
      (values.map some ++ List.replicate f.locals.length (none : Option (Word w))).length := by
    simp only [List.length_append,List.length_map,List.length_replicate,arity]
    unfold Function.frameSize Function.slots at space ⊢
    omega
  obtain ⟨c,⟨n,hs,hr⟩,hm⟩ := d.returns (function := callee) hcap
  refine ⟨c,⟨n+1,?_,hr⟩,hm⟩
  refine Steps.cons (event := none) ?_ hs
  simp [Step,step,enter,lookup,arity,space,Config.stackWords,atStatement]

end RamLang
