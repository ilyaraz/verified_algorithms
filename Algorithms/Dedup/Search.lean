import Algorithms.Dedup.Blocks

namespace Dedup
open WordRam Registers Blocks

/-- Chain search changes only its cursor and two temporary registers. -/
def ScanFrame (s t : State w 64) : Prop :=
  t.mem = s.mem ∧ ∀ r, r ≠ cursor → r ≠ pointer → r ≠ loaded → t.regs r = s.regs r

theorem ScanFrame.refl (s : State w 64) : ScanFrame s s := ⟨rfl, by intros; rfl⟩

theorem ScanFrame.trans {s t u : State w 64} (h : ScanFrame s t) (g : ScanFrame t u) :
    ScanFrame s u := ⟨g.1.trans h.1, fun r hc hp hl => (g.2 r hc hp hl).trans (h.2 r hc hp hl)⟩

theorem scanMatch_frame (s : State w 64) : ScanFrame s (scanMatch s) := by
  constructor
  · rfl
  · intro r hc hp hl
    simp [scanMatch, update, hp, hl]

theorem scanNext_frame (s : State w 64) : ScanFrame s (scanNext s) := by
  constructor
  · rfl
  · intro r hc hp hl
    simp [scanNext, scanMatch, update, hp, hl, hc]

theorem scanAddress_eq {s : State w 64} {base i : Nat}
    (hn : s.regs nodes = word w base) (hc : s.regs cursor = word w i)
    (hi : 0 < i) (hw : 1 < modulus w) : scanAddress s = word w (nodeAddress base i) := by
  unfold scanAddress nodeAddress
  rw [hn, hc, word_sub _ _ hw (by omega), word_mul, word_add]
  congr 1
  omega

/-- Actual chain traversal, charged by comparisons with an additional empty-chain
branch. Only initialized node cells are read; no store or random load occurs. -/
theorem scan_total {w : Nat} (rho : RandomMemory w) {s : State w 64}
    {base n : Nat} {xs : List (Word w × Nat)} {x : Word w}
    (hp : s.pc = 32) (hk : s.regs key = x) (hn : s.regs nodes = word w base)
    (hc : s.regs cursor = word w (firstIndex xs))
    (chainAt : ChainAt s.mem base xs)
    (indices : ∀ p ∈ xs, 0 < p.2 ∧ p.2 ≤ n)
    (fit : (Region.mk base (2*n)).Fits w) (hw : 1 < modulus w) :
    ∃ k t log, Steps program rho k s t log ∧
      k ≤ 9*scanComparisons x (xs.map Prod.fst)+1 ∧
      t.pc = (if x ∈ xs.map Prod.fst then 41 else 44) ∧
      ScanFrame s t ∧
      AccessPolicy.AllowsTrace ⟨(Region.mk base (2*n)).Contains, fun _ => False, fun _ => False⟩ log := by
  induction xs generalizing s with
  | nil =>
    refine ⟨1, {s with pc := 44}, [], scan_empty s rho hp hc, ?_, ?_, ?_, ?_⟩
    · simp [scanComparisons]
    · simp
    · exact ScanFrame.refl s
    · simp [AccessPolicy.AllowsTrace]
  | cons p xs ih =>
    obtain ⟨y,i⟩ := p
    obtain ⟨hy,ht,hr⟩ := chainAt
    have hi := indices (y,i) (by simp)
    have ha := scanAddress_eq hn hc hi.1 hw
    simp only [firstIndex] at ha
    have hcfit := node_contains fit hi.1 hi.2
    have hilt : i < modulus w := by
      unfold Region.Fits at fit
      simp only at fit
      omega
    have hne : s.regs cursor ≠ word w 0 := by
      rw [hc]
      change word w i ≠ word w 0
      intro he
      have hh := congrArg BitVec.toNat he
      rw [word_toNat_of_lt hilt, word_toNat_of_lt (by omega : 0 < modulus w)] at hh
      omega
    have hload : s.mem (scanAddress s) = y := by rw [ha]; exact hy
    have han : scanAddress s+word w 1 = word w (nodeAddress base i+1) := by
      rw [ha, word_add]
    by_cases he : x = y
    · refine ⟨6, scanMatch s, [.dataRead (scanAddress s) y], ?_, ?_, ?_, scanMatch_frame s, ?_⟩
      · simpa [hload] using scan_match s rho hp hne (by rw [hk, hload, he])
      · simp [scanComparisons, he]
      · simp [scanMatch, he]
      · simpa [AccessPolicy.AllowsTrace, AccessPolicy.Allows, ha] using hcfit.1
    · have hs := scan_miss s rho hp hne (by rw [hk, hload]; exact he)
      have fr := scanNext_frame s
      have hn' : (scanNext s).regs nodes = word w base := by
        rw [fr.2 nodes (by decide) (by decide) (by decide), hn]
      have hk' : (scanNext s).regs key = x := by
        rw [fr.2 key (by decide) (by decide) (by decide), hk]
      have hc' : (scanNext s).regs cursor = word w (firstIndex xs) := by
        simp only [scanNext, update_same]
        rw [han]
        exact ht
      obtain ⟨k,t,log,hsteps,hcost,hpc,hframe,htrace⟩ :=
        ih rfl hk' hn' hc' hr (fun p hp => indices p (by simp [hp]))
      refine ⟨9+k,t,_,hs.trans hsteps,?_,?_,fr.trans hframe,?_⟩
      · simp only [List.map_cons, scanComparisons, he, ↓reduceIte]
        omega
      · simpa only [List.map_cons, List.mem_cons, he, false_or] using hpc
      · rw [AccessPolicy.allowsTrace_append]
        refine ⟨?_,htrace⟩
        simp only [AccessPolicy.AllowsTrace, List.mem_cons, List.not_mem_nil, or_false]
        intro e he
        rcases he with rfl | rfl
        · simpa [AccessPolicy.Allows, ha] using hcfit.1
        · simpa [AccessPolicy.Allows, han] using hcfit.2

end Dedup
