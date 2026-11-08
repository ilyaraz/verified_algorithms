import Algorithms.Dedup.Blocks

namespace Dedup.Blocks
open WordRam Registers

def clearMany : Nat → State w 64 → State w 64
  | 0,s => s
  | n+1,s => clearMany n (clearNext s)

def clearTrace : Nat → State w 64 → List (Access w)
  | 0,_ => []
  | n+1,s => [.dataWrite (s.regs clearCursor) (word w 0)] ++ clearTrace n (clearNext s)

@[simp] theorem clearNext_cursor (s : State w 64) :
    (clearNext s).regs clearCursor = s.regs clearCursor+word w 1 := by
  simp [clearNext, update, clearCursor, clearRemaining]

@[simp] theorem clearNext_remaining (s : State w 64) :
    (clearNext s).regs clearRemaining = s.regs clearRemaining-word w 1 := by
  simp [clearNext, update]

theorem clear_countdown {s : State w 64} (hn : s.regs clearRemaining = word w (n+1))
    (hf : n+1 < modulus w) : (clearNext s).regs clearRemaining = word w n := by
  rw [clearNext_remaining, hn, word_sub _ _ (by omega) (by omega)]
  simp

theorem clear_many (rho : RandomMemory w) (n : Nat) {s : State w 64}
    (hp : s.pc = 16) (hn : s.regs clearRemaining = word w n) (hf : n < modulus w) :
    Steps program rho (5*n+1) s {clearMany n s with pc := 21} (clearTrace n s) := by
  induction n generalizing s with
  | zero => simpa [clearMany, clearTrace] using clear_exit s rho hp hn
  | succ n ih =>
    have he : s.regs clearRemaining ≠ word w 0 := by
      rw [hn]
      intro hh
      have ht := congrArg BitVec.toNat hh
      rw [word_toNat_of_lt hf, word_toNat_of_lt (by omega : 0 < modulus w)] at ht
      omega
    have hs := clear_iteration s rho hp he
    have ht := ih (s := clearNext s) rfl (clear_countdown hn hf) (by omega)
    convert hs.trans ht using 1 <;> (try simp [clearMany, clearTrace]) <;> omega

theorem clear_many_register (n : Nat) (s : State w 64) (r : Reg 64)
    (hc : r ≠ clearCursor) (hr : r ≠ clearRemaining) :
    (clearMany n s).regs r = s.regs r := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa [clearMany, clearNext, update, hc, hr] using ih (clearNext s)

theorem clear_frame (n b : Nat) {s : State w 64}
    (hc : s.regs clearCursor = word w b) (hf : b+n < modulus w)
    (ha : ¬ (Region.mk b n).Contains a) : (clearMany n s).mem a = s.mem a := by
  induction n generalizing b s with
  | zero => rfl
  | succ n ih =>
    have hc' : (clearNext s).regs clearCursor = word w (b+1) := by rw [clearNext_cursor,hc,word_add]
    have ha' : ¬ (Region.mk (b+1) n).Contains a := by
      simp only [Region.Contains] at *
      omega
    rw [clearMany, ih (b+1) hc' (by omega) ha']
    change update s.mem (s.regs clearCursor) (word w 0) a = s.mem a
    rw [hc, update_word _ _ _ (by omega)]
    split
    · simp only [Region.Contains] at ha
      omega
    · rfl

theorem clear_array (n b : Nat) {s : State w 64}
    (hc : s.regs clearCursor = word w b) (hf : b+n < modulus w) :
    ArrayAt (clearMany n s).mem b (List.replicate n (word w 0)) := by
  induction n generalizing b s with
  | zero => simp
  | succ n ih =>
    have hc' : (clearNext s).regs clearCursor = word w (b+1) := by rw [clearNext_cursor,hc,word_add]
    rw [List.replicate_succ, arrayAt_cons]
    constructor
    · change (clearMany n (clearNext s)).mem (word w b) = _
      rw [clear_frame n (b+1) hc' (by omega)]
      · simp [clearNext,hc]
      · simp only [Region.Contains, word_toNat_of_lt (by omega : b < modulus w)]
        omega
    · exact ih (b+1) hc' (by omega)

theorem clear_trace (n b : Nat) {s : State w 64}
    (hc : s.regs clearCursor = word w b) (hf : b+n < modulus w) :
    AccessPolicy.AllowsTrace ⟨fun _ => False, (Region.mk b n).Contains, fun _ => False⟩
      (clearTrace n s) := by
  induction n generalizing b s with
  | zero => simp [clearTrace,AccessPolicy.AllowsTrace]
  | succ n ih =>
    rw [clearTrace, AccessPolicy.allowsTrace_append]
    constructor
    · simpa [AccessPolicy.AllowsTrace,AccessPolicy.Allows,hc] using
        Region.contains_index (r := ⟨b,n+1⟩) (i := 0) hf (by omega : 0 < n+1)
    · have hc' : (clearNext s).regs clearCursor = word w (b+1) := by rw [clearNext_cursor,hc,word_add]
      have ht := ih (b+1) hc' (by omega)
      intro e he
      have hh := ht e he
      cases e <;> simp only [AccessPolicy.Allows,Region.Contains] at * <;> omega

@[simp] theorem clear_random (n : Nat) (s : State w 64) :
    (clearTrace n s).filterMap Access.randomAddress = [] := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [clearTrace,ih,Access.randomAddress]

end Dedup.Blocks
