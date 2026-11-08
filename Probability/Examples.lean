import Probability.FiniteSearch
import WordRam.RandomBlocks
import WordRam.Blocks

/-! An actual RAM predicate search: try one random word, then enumerate zero
and one until finding a nonzero word. Both rejected candidates and all fallback
bookkeeping are visible in the instruction count. -/
namespace FiniteProbability.Examples
open WordRam

def result : Reg 2 := ⟨0, by decide⟩
def randomAddress : Reg 2 := ⟨1, by decide⟩

def predicateSearch : Program 2 := #[
  .rload result (.reg randomAddress),
  .branch .ne (.reg result) (.imm 0) 6,
  .mov result (.imm 0),
  .branch .ne (.reg result) (.imm 0) 6,
  .add result (.reg result) (.imm 1),
  .branch .ne (.reg result) (.imm 0) 6,
  .halt]

theorem predicateSearch_exact (rho : RandomMemory w) (rs : Registers w 2) (mem : DataMemory w) :
    run predicateSearch rho 7 (.initial rs mem) =
      ⟨⟨6, update rs result (if rho (rs randomAddress) = word w 0 then word w 1
        else rho (rs randomAddress)), mem⟩,
       if rho (rs randomAddress) = word w 0 then 7 else 3,
       [.randomRead (rs randomAddress) (rho (rs randomAddress))], .halted⟩ := by
  by_cases h : rho (rs randomAddress) = word w 0
  all_goals first
    | change rho (rs (1 : Reg 2)) = word w 0 at h
    | change rho (rs (1 : Reg 2)) ≠ word w 0 at h
  all_goals simp [predicateSearch, run, step, State.initial, State.put, Operand.eval,
    Comparison.test, result, randomAddress, h, update, update_shadow, RunResult.prepend]
  simp [word, BitVec.zero_add]

/-- Every random image succeeds, including one containing only rejected values. -/
theorem predicateSearch_total (hw : 1 ≤ w) (rho : RandomMemory w)
    (rs : Registers w 2) (mem : DataMemory w) :
    let r := run predicateSearch rho 7 (.initial rs mem)
    r.reason = .halted ∧ r.steps ≤ 7 ∧ r.state.regs result ≠ word w 0 ∧
    r.state.mem = mem ∧ r.randomAddresses = [rs randomAddress] ∧
    r.randomAddresses.Nodup ∧ r.dataFootprint = [] := by
  rw [predicateSearch_exact]
  have hp : 1 < modulus w := by
    exact Nat.lt_of_lt_of_le (by decide : 1 < 2)
      (Nat.pow_le_pow_right (n := 2) (by decide) hw)
  have hone : word w 1 ≠ word w 0 := by
    intro he
    have := congrArg BitVec.toNat he
    simp [word_toNat_of_lt hp] at this
  simp only [update_same, RunResult.randomAddresses, RunResult.dataFootprint,
    List.filterMap_cons, List.filterMap_nil, Access.randomAddress, Access.dataAddress,
    List.eraseDups_nil, List.nodup_cons, List.not_mem_nil, List.nodup_nil,
    and_true, true_and]
  split <;> simp_all

/-- Even interrupted runs respect their one-cell random reservation and cannot
fault. The same random image is used for every interpreter prefix. -/
theorem predicateSearch_prefix (rho : RandomMemory w) (rs : Registers w 2)
    (mem : DataMemory w) (fuel : Nat) :
    AccessPolicy.AllowsTrace ⟨fun _ => False, fun _ => False, fun a => a = rs randomAddress⟩
      (run predicateSearch rho fuel (.initial rs mem)).trace ∧
    ∀ f, (run predicateSearch rho fuel (.initial rs mem)).reason ≠ .fault f := by
  have hh : (run predicateSearch rho 7 (.initial rs mem)).reason = .halted := by
    rw [predicateSearch_exact]
  have ht := terminatesIn_of_halted hh
  constructor
  · apply ht.prefix_policy
    simp [predicateSearch_exact, AccessPolicy.AllowsTrace, AccessPolicy.Allows]
  · exact fun f => ht.noFault fuel f

/-- A caller can reserve exactly one fitting random cell. Every fuel prefix
respects that reservation, including the deterministic fallback. -/
theorem predicateSearch_reservation (rho : RandomMemory w) (rs : Registers w 2)
    (mem : DataMemory w) (hf : base+1 < modulus w)
    (ha : rs randomAddress = word w base) (fuel : Nat) :
    AccessPolicy.AllowsTrace
      ⟨fun _ => False, fun _ => False, (Region.mk base 1).Contains⟩
      (run predicateSearch rho fuel (.initial rs mem)).trace := by
  have ht := (predicateSearch_prefix rho rs mem fuel).1
  intro e he
  have hp := ht e he
  cases e with
  | dataRead a v => exact hp
  | dataWrite a v => exact hp
  | randomRead a v =>
    change a = rs randomAddress at hp
    change (Region.mk base 1).Contains a
    rw [hp, ha]
    exact Region.contains_index (r := ⟨base, 1⟩) (i := 0) hf (by simp)

/-- Exact expected cost under the original complete-memory uniform law. -/
theorem predicateSearch_expected (rs : Registers w 2) (mem : DataMemory w) :
    expectedSteps predicateSearch 7 (.initial rs mem) = 3 + 4/(modulus w : ℝ) := by
  change mean (fun rho : RandomMemory w => (run predicateSearch rho 7 (.initial rs mem)).steps) = _
  have he : ∀ rho : RandomMemory w, ((run predicateSearch rho 7 (.initial rs mem)).steps : ℝ) =
      if rho (rs randomAddress) = word w 0 then (7 : ℝ) else 3 := by
    intro rho
    rw [predicateSearch_exact]
    split <;> rfl
  rw [mean_congr he, mean_ite]
  rw [← RandomBlocks.probability_eq_finite, WordRam.probability_cell]
  ring

theorem predicateSearch_expected_le (hw : 1 ≤ w) (rs : Registers w 2) (mem : DataMemory w) :
    expectedSteps predicateSearch 7 (.initial rs mem) ≤ 5 := by
  rw [predicateSearch_expected]
  have hp : 2 ≤ modulus w := Nat.pow_le_pow_right (n := 2) (by decide) hw
  have hp' : (2 : ℝ) ≤ modulus w := by exact_mod_cast hp
  have h := (div_le_iff₀ (by linarith : (0 : ℝ) < modulus w)).mpr
    (show (4 : ℝ) ≤ 2 * modulus w by linarith)
  linarith

theorem predicateSearch_forced_fallback :
    let r := run predicateSearch (zeroMemory 2) 7 (State.zero 2 2)
    r.reason = .halted ∧ r.steps = 7 ∧ r.state.regs result = word 2 1 ∧ r.randomReads = 1 := by decide

theorem predicateSearch_random_success :
    let r := run predicateSearch (fun _ => word 2 3) 7 (State.zero 2 2)
    r.reason = .halted ∧ r.steps = 3 ∧ r.state.regs result = word 2 3 ∧ r.randomReads = 1 := by decide

theorem repeated_address_not_injective :
    ¬ Function.Injective (fun _ : Fin 2 => word 4 3) := by
  intro h
  have := congrArg Fin.val (h (a₁ := ⟨0, by decide⟩) (a₂ := ⟨1, by decide⟩) rfl)
  contradiction

end FiniteProbability.Examples
