import Algorithms.Dedup.Loop
import Algorithms.Dedup.Clear
import Algorithms.Dedup.Round

namespace Dedup
open WordRam Registers Blocks
open Hashing.PowerOfTwo

variable {w N : Nat} {l : Layout}

theorem Admissible.count_fit (ha : Admissible w N l) : N < modulus w := by
  have hh := ha.workspace
  simp only [Layout.workspace,workspaceCapacity,Region.Fits] at hh
  omega

theorem Admissible.bucket_bits (ha : Admissible w N l) : bits N ≤ w :=
  least (Nat.le_of_lt ha.count_fit)

theorem Admissible.bucket_fit (ha : Admissible w N l) : Hashing.PowerOfTwo.size N < modulus w := by
  have hh := ha.workspace
  have hc := conservative N
  simp only [Layout.workspace,workspaceCapacity,Region.Fits] at hh
  omega

/-- Parameters computed by rounding and the one-cell odd-seed sampler. -/
def parameters (ha : Admissible w N l) (raw : Word w) : HashParameters w N where
  seed := Hashing.MultiplyShift.sample raw
  shift := word w (w-bits N)
  slots := Hashing.PowerOfTwo.size N
  hash x := (Hashing.MultiplyShift.eval (Hashing.MultiplyShift.sample raw) x (bits N)).toNat
  range x := Hashing.MultiplyShift.eval_range _ x ha.bucket_bits
  capacity := conservative N
  realizes x := by
    have hc : (word w (w-bits N)).toNat = w-bits N :=
      word_toNat_of_lt ((Nat.sub_le w _).trans_lt ha.width)
    simp only [unsignedShiftRight,hc]
    change Hashing.MultiplyShift.eval _ x (bits N) = word w (Hashing.MultiplyShift.eval _ x (bits N)).toNat
    simp only [word,BitVec.ofNat_toNat,BitVec.setWidth_eq]

/-- Initialization reads exactly the dedicated random cell and writes only the
bucket directory, charging all clearing of initially dirty memory. -/
theorem initialization (ha : Admissible w N l) (rho : RandomMemory w)
    (xs : List (Word w)) (hx : xs.length = N) {s : State w 64}
    (hp : s.pc = 0) (hin : Input w N l s.regs) (arr : ArrayAt s.mem l.input xs) :
    ∃ k t log, Steps program rho k s t log ∧ k ≤ 14*N+28 ∧
      LoopInvariant N l (parameters ha (rho (word w l.random))) [] xs t ∧
      (AccessPolicy.mk (fun _ => False) (l.workspace N).Contains
        (fun a => a = word w l.random)).AllowsTrace log ∧
      log.filterMap Access.randomAddress = [word w l.random] := by
  obtain ⟨hinp,hcount,hscratch,hrandom,hwidth⟩ := hin
  change s.regs Registers.input = word w l.input at hinp
  change s.regs count = word w N at hcount
  change s.regs scratch = word w l.scratch at hscratch
  change s.regs random = word w l.random at hrandom
  change s.regs width = word w w at hwidth
  have hcount' : (entryNext s).regs count = word w N := by
    simpa [entryNext,update,count,heads,remaining,distinct,Registers.size,shift] using hcount
  have hsize : (entryNext s).regs Registers.size = word w (2^0) := by
    simp [entryNext,update,Registers.size,shift]
  have hshift : (entryNext s).regs shift = word w (w-0) := by
    simpa [entryNext] using hwidth
  obtain ⟨r,hr,rpost⟩ := round_many rho N 0 (bits N) rfl hcount' hsize hshift (by omega)
    ha.bucket_bits ha.bucket_fit ha.width
  have rcore (j : Reg 64) (hs : j ≠ Registers.size) (hh : j ≠ shift) :
      r.regs j = (entryNext s).regs j := rpost.registers j hs hh
  have rcount : r.regs count = word w N := by rw [rcore _ (by decide) (by decide),hcount']
  have rheads : r.regs heads = word w l.scratch := by
    rw [rcore _ (by decide) (by decide)]
    simpa [entryNext,update,heads,remaining,distinct,Registers.size,shift] using hscratch
  let c := roundedNext r
  have cnodes : c.regs nodes = word w (l.nodes N).base := by
    have hn : roundedNodes r = word w (l.nodes N).base := by
      unfold roundedNodes
      rw [rheads,rcount,word_add,word_mul,word_add]
      congr 1
      simp [Layout.nodes,Nat.mul_comm]
    simpa [c,roundedNext,update,nodes,temp,compact,clearCursor,clearRemaining] using hn
  have ccompact : c.regs compact = word w (l.compact N).base := by
    have hc : roundedNodes r+r.regs count*word w 2 = word w (l.compact N).base := by
      unfold roundedNodes
      rw [rheads,rcount,word_add,word_mul,word_add,word_mul,word_add]
      congr 1
      simp [Layout.compact,Nat.mul_comm]
    simpa [c,roundedNext,update,compact,clearCursor,clearRemaining] using hc
  have ccursor : c.regs clearCursor = word w l.scratch := by
    simpa [c,roundedNext,update,clearCursor,clearRemaining] using rheads
  have crem : c.regs clearRemaining = word w (Hashing.PowerOfTwo.size N) := by
    simpa [c,roundedNext] using rpost.size
  let m := Hashing.PowerOfTwo.size N
  let a := {clearMany m c with pc := 21}
  have clear := clear_many rho m rfl crem ha.bucket_fit
  have hfit : l.scratch+m < modulus w := by
    have hh := ha.workspace
    have hm := conservative N
    simp only [Layout.workspace,workspaceCapacity,Region.Fits] at hh
    change l.scratch+Hashing.PowerOfTwo.size N < modulus w
    omega
  have acore (j : Reg 64) (hc : j ≠ clearCursor) (hr : j ≠ clearRemaining) :
      a.regs j = c.regs j := clear_many_register m c j hc hr
  have arandom : a.regs random = word w l.random := by
    rw [acore _ (by decide) (by decide)]
    change (roundedNext r).regs random = _
    simp only [roundedNext]
    simp [update,random,nodes,temp,compact,clearCursor,clearRemaining]
    rw [rcore _ (by decide) (by decide)]
    simpa [entryNext,update,random,heads,remaining,distinct,Registers.size,shift] using hrandom
  let t := sampleNext rho a
  have tcore (j : Reg 64) (ht : j ≠ temp) (hs : j ≠ seed)
      (hc : j ≠ clearCursor) (hr : j ≠ clearRemaining) : t.regs j = c.regs j := by
    change (sampleNext rho a).regs j = _
    simp only [sampleNext,update,ht,hs,↓reduceIte]
    exact acore j hc hr
  have inv : LoopInvariant N l (parameters ha (rho (word w l.random))) [] xs t := by
    constructor
    · constructor
      · rw [tcore _ (by decide) (by decide) (by decide) (by decide)]
        change (roundedNext r).regs Registers.input = _
        simp [roundedNext,update,Registers.input,nodes,temp,compact,clearCursor,clearRemaining]
        rw [rcore _ (by decide) (by decide)]
        simpa [entryNext,update,Registers.input,heads,remaining,distinct,Registers.size,shift,hx] using hinp
      · rw [tcore _ (by decide) (by decide) (by decide) (by decide)]
        change (roundedNext r).regs remaining = _
        simp [roundedNext,update,remaining,nodes,temp,compact,clearCursor,clearRemaining]
        rw [rcore _ (by decide) (by decide)]
        simpa [entryNext,update,remaining,distinct,Registers.size,shift,hx] using hcount
      · rw [tcore _ (by decide) (by decide) (by decide) (by decide)]
        change (roundedNext r).regs distinct = _
        simp [roundedNext,update,distinct,nodes,temp,compact,clearCursor,clearRemaining]
        rw [rcore _ (by decide) (by decide)]
        simp [entryNext,update,distinct,Registers.size,shift]
      · rw [tcore _ (by decide) (by decide) (by decide) (by decide)]
        simpa [c,roundedNext,update,heads,nodes,temp,compact,clearCursor,clearRemaining] using rheads
      · rw [tcore _ (by decide) (by decide) (by decide) (by decide),cnodes]
      · rw [tcore _ (by decide) (by decide) (by decide) (by decide),ccompact]
      · change Hashing.MultiplyShift.sample (rho (a.regs random)) = _
        rw [arandom]
        rfl
      · rw [tcore _ (by decide) (by decide) (by decide) (by decide)]
        simpa [c,roundedNext,update,shift,nodes,temp,compact,clearCursor,clearRemaining] using rpost.shift
    · rfl
    · simp [hx]
    · simp only [hx,Nat.sub_self,Nat.add_zero]
      intro i
      change (clearMany m c).mem (word w (l.input+i.val)) = xs[i]
      rw [clear_frame m l.scratch ccursor hfit]
      · change r.mem _ = _
        rw [rpost.memory]
        exact arr i
      · have hc : (l.inputRegion N).Contains (word w (l.input+i.val)) :=
          Region.contains_index ha.input (by have := i.isLt; simpa [hx] using this)
        have hn := Region.not_contains_of_separated ha.separated hc
        simp only [Region.Contains,Layout.workspace,workspaceCapacity] at *
        have hm := conservative N
        change ¬ (l.scratch ≤ _ ∧ _ < l.scratch+m)
        omega
    · exact Representation.empty (clear_array m l.scratch ccursor hfit)
  have allsteps := (((entry_next s rho hp).trans hr).trans (rounded_next r rho rpost.pc)).trans
    (clear.trans (sample_next a rho rfl))
  refine ⟨_,t,_,allsteps,?_,inv,?_,?_⟩
  · have hb := bits_le_input N
    have hm := conservative N
    change 5+(4*bits N+1)+7+(5*m+1+4) ≤ 14*N+28
    dsimp [m]
    omega
  · simp only [List.nil_append,AccessPolicy.allowsTrace_append]
    constructor
    · have hc := clear_trace m l.scratch ccursor hfit
      intro e he
      have hh := hc e he
      cases e <;> simp only [AccessPolicy.Allows] at *
      simp only [Region.Contains,Layout.workspace,workspaceCapacity] at *
      have hm := conservative N
      change l.scratch ≤ _ ∧ _ < l.scratch+6*(N+1)
      constructor <;> omega
    · simp [AccessPolicy.AllowsTrace,AccessPolicy.Allows,arandom]
  · simp [clear_random,arandom,Access.randomAddress]

end Dedup
