import RamLang.Compiler.Proofs.SimulationBase

namespace RamLang.Compiler
open WordRam ABI

/-- Compositional compiler contract at any linked statement boundary. The free
capacity is measured after the current frame, and extra is historical peak use. -/
def Implements (code : WordRam.Program registers) (rho : RandomMemory w)
    (frames entries : FunctionId → Nat) (exhausted : Nat) (stack : Region)
    (free : Nat) (stmt : Stmt) (locals : Locals w) (mem : DataMemory w)
    (flow : Flow w) (mem' : DataMemory w) (observed : List (Access w)) (work extra : Nat) : Prop :=
  ∀ base savedFP returnPC (s : State w registers),
    FrameState stack base locals savedFP returnPC mem s →
    free = stack.base+stack.size-(base+2+locals.length) → returnPC < modulus w →
    CodeAt code s.pc (lower frames entries exhausted s.pc stmt) →
    ∃ t trace, Fragment code rho stack base (base+2+locals.length+extra) savedFP returnPC
      (s.pc+size stmt) flow mem' observed work s t trace

variable {w free : Nat} {code : WordRam.Program registers} {rho : RandomMemory w}
  {frames entries : FunctionId → Nat} {exhausted : Nat} {stack : Region}
  {locals middle : Locals w} {mem mem₁ mem₂ : DataMemory w}
  {flow : Flow w} {log₁ log₂ : List (Access w)} {a b : Stmt} {n m extra₁ extra₂ : Nat}

/-- Empty source syntax consumes no target instruction. -/
theorem implements_skip : Implements code rho frames entries exhausted stack free .skip locals mem
    (.next locals) mem [] 0 0 := by
  intro base savedFP returnPC s hf hfree hret hc
  refine ⟨s,[],⟨.refl _,?_,rfl,?_,?_⟩⟩
  · exact ⟨by simp [size],hf⟩
  · simp [AccessPolicy.AllowsTrace]
  · exact StackBound.zero (hf.sp_le (by omega))

theorem implements_primitive {op : Primitive} {locals' : Locals w} {event : Option (Access w)}
    (he : op.eval rho locals mem = .ok (locals',mem₁,event)) (hsep : Separated stack event.toList) :
    Implements code rho frames entries exhausted stack free (.primitive op) locals mem
      (.next locals') mem₁ event.toList (primitive op).length 0 := by
  intro base savedFP returnPC s hf hfree hret hc
  obtain ⟨t,trace,hs,hpc,hf',hproj,hpol⟩ := primitive_steps he hsep hf hc
  refine ⟨t,trace,⟨hs,⟨hpc,hf'⟩,hproj,?_,primitive_stackBound hf hc (by omega)⟩⟩
  simpa only [Primitive.length he,Nat.add_zero] using hpol

/-- Sequencing combines exact work by addition and stack peaks by maximum. -/
theorem implements_sequence
    (ha : Implements code rho frames entries exhausted stack free a locals mem (.next middle) mem₁ log₁ n extra₁)
    (hb : Implements code rho frames entries exhausted stack free b middle mem₁ flow mem₂ log₂ m extra₂)
    (hlen : middle.length = locals.length) :
    Implements code rho frames entries exhausted stack free (.seq a b) locals mem flow mem₂
      (log₁++log₂) (n+m) (max extra₁ extra₂) := by
  intro base savedFP returnPC s hf hfree hret hc
  obtain ⟨t,trace₁,h₁⟩ := ha base savedFP returnPC s hf hfree hret hc.prefix
  obtain ⟨hpc₁,hf₁⟩ := h₁.post
  obtain ⟨u,trace₂,h₂⟩ := hb base savedFP returnPC t hf₁ (by simpa only [hlen] using hfree) hret (by
    rw [hpc₁]; simpa only [lower_length] using hc.suffix)
  refine ⟨u,trace₁++trace₂,⟨h₂.execution.prepend h₁.execution,?_,?_,?_,?_⟩⟩
  · have he : s.pc+size (.seq a b) = t.pc+size b := by rw [hpc₁]; simp [size,Nat.add_assoc]
    rw [he]; exact h₂.post
  · rw [project_append,h₁.projection,h₂.projection]
  · exact (AccessPolicy.allowsTrace_append _).mpr
      ⟨framePolicy_mono (Nat.le_refl _) (by omega) h₁.policy,
       framePolicy_mono (Nat.le_refl _) (by omega) h₂.policy⟩
  · exact StackBound.trans h₁.execution (h₁.stackBound.mono (by omega)) (h₂.stackBound.mono (by omega))

/-- Early return and exhaustion discard the remaining structured continuation. -/
theorem implements_sequenceStop (hs : flow.stops)
    (ha : Implements code rho frames entries exhausted stack free a locals mem flow mem₁ log₁ n extra₁) :
    Implements code rho frames entries exhausted stack free (.seq a b) locals mem flow mem₁ log₁ n extra₁ := by
  intro base savedFP returnPC s hf hfree hret hc
  obtain ⟨t,trace,h⟩ := ha base savedFP returnPC s hf hfree hret hc.prefix
  exact ⟨t,trace,⟨h.execution,h.post.changeEnd hs _,h.projection,h.policy,h.stackBound⟩⟩

theorem implements_return {x : Atom} {v : Word w} (hx : x.eval locals = .ok v) :
    Implements code rho frames entries exhausted stack free (.ret x) locals mem (.returned v) mem []
      ((atom result x).length+epilogue.length) 0 := by
  intro base savedFP returnPC s hf hfree hret hc
  obtain ⟨t,trace,hs,hpc,hfp,hsp,hv,hl,hm,hproj,hpol⟩ := return_steps hx hf hret hc
  exact ⟨t,trace,⟨hs,⟨hpc,hfp,hsp,hv,hl,hm⟩,hproj,by simpa only [Nat.add_zero] using hpol,return_stackBound hf hc (by omega)⟩⟩

/-- Conditional true branches jump directly to the emitted yes body. -/
theorem implements_ifTrue {c : Condition} (htest : c.eval locals = .ok true)
    (ha : Implements code rho frames entries exhausted stack free a locals mem flow mem₁ log₁ n extra₁) :
    Implements code rho frames entries exhausted stack free (.ite c a b) locals mem flow mem₁ log₁
      (conditionCost c+1+n) extra₁ := by
  intro base savedFP returnPC s hf hfree hret hc
  let test := atom left c.left ++ atom right c.right
  let noPC := s.pc+test.length+1
  let yesPC := noPC+size b+1
  change CodeAt code s.pc (((test ++ [.branch c.comparison (.reg left) (.reg right) yesPC]) ++
    lower frames entries exhausted noPC b ++ [.jump (yesPC+size a)]) ++
    lower frames entries exhausted yesPC a) at hc
  obtain ⟨t,trace₁,hs,hpc,hf₁,hproj,hpol⟩ := condition_steps htest hf hc.prefix.prefix.prefix
  simp at hpc
  have hyes : CodeAt code t.pc (lower frames entries exhausted t.pc a) := by
    rw [hpc]
    have he : s.pc + ((test ++ [Instr.branch c.comparison (.reg left) (.reg right) yesPC]) ++
        lower frames entries exhausted noPC b ++ [Instr.jump (yesPC+size a)]).length = yesPC := by
      simp only [List.length_append,List.length_cons,List.length_nil,lower_length]
      dsimp [yesPC,noPC]
      omega
    simpa only [he] using hc.suffix
  obtain ⟨u,trace₂,h₂⟩ := ha base savedFP returnPC t hf₁ hfree hret hyes
  refine ⟨u,trace₁++trace₂,⟨h₂.execution.prepend hs,?_,?_,?_,?_⟩⟩
  · have he : s.pc+size (.ite c a b) = t.pc+size a := by
      rw [hpc]; simp only [size,test,yesPC,noPC,List.length_append]; omega
    rw [he]; exact h₂.post
  · rw [project_append,hproj,h₂.projection,List.nil_append]
  · exact (AccessPolicy.allowsTrace_append _).mpr
      ⟨framePolicy_mono (Nat.le_refl _) (by omega) hpol,h₂.policy⟩
  · exact StackBound.trans hs
      (condition_stackBound hc.prefix.prefix.prefix hs (hf.sp_le (by omega)) (hf₁.sp_le (by omega))) h₂.stackBound

/-- False branches pay their trailing jump only when they continue normally. -/
theorem implements_ifFalse {c : Condition} (htest : c.eval locals = .ok false)
    (hb : Implements code rho frames entries exhausted stack free b locals mem flow mem₁ log₁ n extra₁) :
    Implements code rho frames entries exhausted stack free (.ite c a b) locals mem flow mem₁ log₁
      (conditionCost c+1+n+(if flow.continues then 1 else 0)) extra₁ := by
  intro base savedFP returnPC s hf hfree hret hc
  let test := atom left c.left ++ atom right c.right
  let noPC := s.pc+test.length+1
  let yesPC := noPC+size b+1
  change CodeAt code s.pc (((test ++ [.branch c.comparison (.reg left) (.reg right) yesPC]) ++
    lower frames entries exhausted noPC b ++ [.jump (yesPC+size a)]) ++
    lower frames entries exhausted yesPC a) at hc
  obtain ⟨t,trace₁,hs,hpc,hf₁,hproj,hpol⟩ := condition_steps htest hf hc.prefix.prefix.prefix
  simp at hpc
  have htpc : t.pc = noPC := by simpa [noPC,test,conditionCost] using hpc
  have hno : CodeAt code t.pc (lower frames entries exhausted t.pc b) := by
    rw [htpc]
    simpa only [List.length_append,List.length_singleton,Nat.add_assoc] using hc.prefix.prefix.suffix
  obtain ⟨u,trace₂,h₂⟩ := hb base savedFP returnPC t hf₁ hfree hret hno
  have hpref := h₂.execution.prepend hs
  have hproject : projectTrace stack (trace₁++trace₂) = log₁ := by
    rw [project_append,hproj,h₂.projection,List.nil_append]
  have hpolicy : (framePolicy stack base (base+2+locals.length+extra₁)).AllowsTrace (trace₁++trace₂) :=
    (AccessPolicy.allowsTrace_append _).mpr ⟨framePolicy_mono (Nat.le_refl _) (by omega) hpol,h₂.policy⟩
  have hbound := StackBound.trans hs
    (condition_stackBound hc.prefix.prefix.prefix hs (hf.sp_le (by omega)) (hf₁.sp_le (by omega))) h₂.stackBound
  cases flow with
  | next out =>
    obtain ⟨hupc,huframe⟩ := h₂.post
    have hjump : CodeAt code u.pc [.jump (yesPC+size a)] := by
      rw [hupc,htpc]
      simpa only [List.length_append,List.length_singleton,lower_length,noPC,Nat.add_assoc] using hc.prefix.suffix
    have hstep := jump_step (rho := rho) hjump
    have hub := hbound.end hpref
    refine ⟨{u with pc := yesPC+size a},trace₁++trace₂,⟨?_,⟨?_,huframe.pc _⟩,hproject,hpolicy,?_⟩⟩
    · simpa [TargetRun,Flow.continues] using
        (show WordRam.Steps code rho (conditionCost c+1+n) s u (trace₁++trace₂) from hpref).trans
          (.cons hstep (.refl _))
    · simp only [size,yesPC,noPC,test,List.length_append]; omega
    · exact StackBound.trans hpref hbound (StackBound.single hstep hub hub)
  | returned v =>
    exact ⟨u,trace₁++trace₂,⟨by simpa [Flow.continues] using hpref,
      h₂.post,hproject,hpolicy,by simpa [Flow.continues] using hbound⟩⟩
  | exhausted =>
    exact ⟨u,trace₁++trace₂,⟨by simpa [Flow.continues] using hpref,
      h₂.post,hproject,hpolicy,by simpa [Flow.continues] using hbound⟩⟩

/-- A false loop test takes the explicit loop-exit jump. -/
theorem implements_whileFalse {c : Condition} (htest : c.eval locals = .ok false) :
    Implements code rho frames entries exhausted stack free (.while c a) locals mem (.next locals) mem []
      (conditionCost c+2) 0 := by
  intro base savedFP returnPC s hf hfree hret hc
  let test := atom left c.left ++ atom right c.right
  let bodyPC := s.pc+test.length+2
  change CodeAt code s.pc ((test ++ [.branch c.comparison (.reg left) (.reg right) bodyPC,
    .jump (bodyPC+size a+1)]) ++ lower frames entries exhausted bodyPC a ++ [.jump s.pc]) at hc
  have hcond : CodeAt code s.pc (test ++ [.branch c.comparison (.reg left) (.reg right) bodyPC]) := by
    have hh := hc.prefix.prefix
    have hh' : CodeAt code s.pc ((test ++ [.branch c.comparison (.reg left) (.reg right) bodyPC]) ++
      [.jump (bodyPC+size a+1)]) := by simpa only [List.append_assoc] using hh
    exact hh'.prefix
  obtain ⟨t,trace,hs,hpc,hf₁,hproj,hpol⟩ := condition_steps htest hf hcond
  have hjump : CodeAt code t.pc [.jump (bodyPC+size a+1)] := by
    rw [hpc]
    have hh := hc.prefix.prefix
    have hh' : CodeAt code s.pc ((test ++ [.branch c.comparison (.reg left) (.reg right) bodyPC]) ++
      [.jump (bodyPC+size a+1)]) := by simpa only [List.append_assoc] using hh
    simpa only [conditionCost,test,List.length_append,List.length_singleton,Nat.add_assoc] using hh'.suffix
  refine ⟨{t with pc := bodyPC+size a+1},trace,⟨?_,⟨?_,hf₁.pc _⟩,hproj,?_,?_⟩⟩
  · simpa [TargetRun,Nat.add_assoc] using hs.trans (.cons (jump_step hjump) (.refl _))
  · simp only [size,bodyPC,test,List.length_append]; omega
  · simpa only [Nat.add_zero] using hpol
  · have hh := StackBound.trans hs
      (condition_stackBound (top := base+2+locals.length+0) hcond hs (hf.sp_le (by omega)) (hf₁.sp_le (by omega)))
      (StackBound.single (jump_step hjump) (hf₁.sp_le (by omega)) (hf₁.sp_le (by omega)))
    simpa only [Nat.add_assoc] using hh

/-- Final-address loop layout: a test, an exit jump, one body, and one back edge. -/
theorem while_parts {c : Condition} {pc : Nat}
    (hc : CodeAt code pc (lower frames entries exhausted pc (.while c a))) :
    CodeAt code pc ((atom left c.left ++ atom right c.right) ++
      [.branch c.comparison (.reg left) (.reg right) (pc+conditionCost c+2)]) ∧
    CodeAt code (pc+conditionCost c+2)
      (lower frames entries exhausted (pc+conditionCost c+2) a) ∧
    CodeAt code (pc+conditionCost c+2+size a) [.jump pc] := by
  let test := atom left c.left ++ atom right c.right
  have he : test.length = conditionCost c := by simp [test,conditionCost]
  change CodeAt code pc ((test ++ [.branch c.comparison (.reg left) (.reg right) (pc+test.length+2),
    .jump (pc+test.length+2+size a+1)]) ++
      lower frames entries exhausted (pc+test.length+2) a ++ [.jump pc]) at hc
  rw [he] at hc
  have hpre : CodeAt code pc ((test ++
      [.branch c.comparison (.reg left) (.reg right) (pc+conditionCost c+2)]) ++
        [.jump (pc+conditionCost c+2+size a+1)]) := by
    simpa only [List.append_assoc] using hc.prefix.prefix
  refine ⟨hpre.prefix,?_,?_⟩
  · simpa only [List.length_append,List.length_cons,List.length_nil,he,Nat.add_assoc] using hc.prefix.suffix
  · simpa only [List.length_append,List.length_cons,List.length_nil,he,lower_length,Nat.zero_add,Nat.reduceAdd,Nat.add_assoc] using hc.suffix

/-- A continuing loop iteration charges its test and back edge before the tail. -/
theorem implements_whileContinue {c : Condition} (htest : c.eval locals = .ok true)
    (ha : Implements code rho frames entries exhausted stack free a locals mem (.next middle) mem₁ log₁ n extra₁)
    (hb : Implements code rho frames entries exhausted stack free (.while c a) middle mem₁ flow mem₂ log₂ m extra₂)
    (hlen : middle.length = locals.length) :
    Implements code rho frames entries exhausted stack free (.while c a) locals mem flow mem₂ (log₁++log₂)
      (conditionCost c+2+n+m) (max extra₁ extra₂) := by
  intro base savedFP returnPC s hf hfree hret hc
  obtain ⟨htestCode,hbodyCode,hbackCode⟩ := while_parts hc
  obtain ⟨t,trace₁,hs,hpc,hf₁,hproj,hpol⟩ := condition_steps htest hf htestCode
  simp at hpc
  obtain ⟨u,trace₂,h₂⟩ := ha base savedFP returnPC t hf₁ hfree hret (by rw [hpc]; exact hbodyCode)
  obtain ⟨hupc,huframe⟩ := h₂.post
  have hjump : CodeAt code u.pc [.jump s.pc] := by rw [hupc,hpc]; exact hbackCode
  let v : State w registers := {u with pc := s.pc}
  obtain ⟨z,trace₃,h₃⟩ := hb base savedFP returnPC v (huframe.pc _) (by simpa only [hlen] using hfree) hret hc
  have hpref : WordRam.Steps code rho (conditionCost c+2+n) s v (trace₁++trace₂) := by
    have hh := (hs.trans h₂.execution).trans (.cons (jump_step hjump) (.refl _))
    have hn : conditionCost c+1+n+(0+1) = conditionCost c+2+n := by omega
    simpa only [hn,Option.toList_none,List.nil_append,List.append_nil] using hh
  refine ⟨z,(trace₁++trace₂)++trace₃,⟨h₃.execution.prepend hpref,h₃.post,?_,?_,?_⟩⟩
  · rw [project_append,project_append,hproj,h₂.projection,h₃.projection,List.nil_append]
  · exact (AccessPolicy.allowsTrace_append _).mpr
      ⟨(AccessPolicy.allowsTrace_append _).mpr
        ⟨framePolicy_mono (Nat.le_refl _) (by omega) hpol,
          framePolicy_mono (Nat.le_refl _) (by omega) h₂.policy⟩,
        framePolicy_mono (Nat.le_refl _) (by omega) h₃.policy⟩
  · have hb₂ := h₂.stackBound.mono (show base+2+locals.length+extra₁ ≤ base+2+locals.length+max extra₁ extra₂ by omega)
    have hub := hb₂.end h₂.execution
    have hbprefix := StackBound.trans (hs.trans h₂.execution)
      (StackBound.trans hs (condition_stackBound htestCode hs (hf.sp_le (by omega)) (hf₁.sp_le (by omega))) hb₂)
      (StackBound.single (jump_step hjump) hub hub)
    have hn : conditionCost c+1+n+1 = conditionCost c+2+n := by omega
    rw [hn] at hbprefix
    exact StackBound.trans hpref hbprefix (h₃.stackBound.mono (by omega))

/-- Early exit inside a loop bypasses the loop's back edge. -/
theorem implements_whileStop {c : Condition} (htest : c.eval locals = .ok true) (hstop : flow.stops)
    (ha : Implements code rho frames entries exhausted stack free a locals mem flow mem₁ log₁ n extra₁) :
    Implements code rho frames entries exhausted stack free (.while c a) locals mem flow mem₁ log₁
      (conditionCost c+1+n) extra₁ := by
  intro base savedFP returnPC s hf hfree hret hc
  obtain ⟨htestCode,hbodyCode,_⟩ := while_parts hc
  obtain ⟨t,trace₁,hs,hpc,hf₁,hproj,hpol⟩ := condition_steps htest hf htestCode
  simp at hpc
  obtain ⟨u,trace₂,h₂⟩ := ha base savedFP returnPC t hf₁ hfree hret (by rw [hpc]; exact hbodyCode)
  refine ⟨u,trace₁++trace₂,⟨h₂.execution.prepend hs,h₂.post.changeEnd hstop _,?_,?_,?_⟩⟩
  · rw [project_append,hproj,h₂.projection,List.nil_append]
  · exact (AccessPolicy.allowsTrace_append _).mpr
      ⟨framePolicy_mono (Nat.le_refl _) (by omega) hpol,h₂.policy⟩
  · exact StackBound.trans hs
      (condition_stackBound htestCode hs (hf.sp_le (by omega)) (hf₁.sp_le (by omega))) h₂.stackBound

end RamLang.Compiler
