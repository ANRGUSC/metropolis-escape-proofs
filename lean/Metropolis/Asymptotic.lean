import Metropolis.AsymptoticKernel
import Metropolis.Shell
import Mathlib.Analysis.Asymptotics.Defs

open Filter Finset
open scoped Asymptotics

namespace Metropolis.Asymptotic

/-- Uniform bounds on the positive cumulative shell mass in the factored sum. -/
theorem shell_factor_bounds (D : ℕ) {p : ℝ} (hp : 0 < p) (hp' : p < 1) (k : ℕ) :
    1 ≤ 1 + ∑ m ∈ range k, Shell.shellSize D (m+1) * p^(m+1) ∧
    1 + ∑ m ∈ range k, Shell.shellSize D (m+1) * p^(m+1) ≤
      1 + 3^D * ∑' m, weight D p m := by
  have bounds (m : ℕ) :
      0 ≤ Shell.shellSize D (m+1) ∧ Shell.shellSize D (m+1) ≤ 3^D * ((m:ℝ)+1)^D := by
    simp only [Shell.shellSize, Nat.add_one_ne_zero, if_false, Nat.cast_add, Nat.cast_one]
    have hbase : 0 ≤ 2*((m:ℝ)+1)-1 := by linarith [Nat.cast_nonneg (α:=ℝ) m]
    constructor
    · exact sub_nonneg.mpr (pow_le_pow_left₀ hbase (by linarith) D)
    · rw [← mul_pow]
      exact (sub_le_self _ (pow_nonneg hbase _)).trans
        (pow_le_pow_left₀ (by positivity) (by linarith [Nat.cast_nonneg (α:=ℝ) m]) D)
  constructor
  · exact le_add_of_nonneg_right (sum_nonneg fun m _ => mul_nonneg (bounds m).1 (pow_nonneg hp.le _))
  · apply add_le_add_right
    calc _ ≤ ∑ m ∈ range k, 3^D * weight D p m := by
           apply sum_le_sum
           intro m _
           unfold weight
           rw [← mul_assoc]
           apply mul_le_mul (bounds m).2 _ (by positivity) (by positivity)
           rw [pow_succ]
           exact mul_le_of_le_one_right (pow_nonneg hp.le _) hp'.le
         _ = 3^D * (∑ m ∈ range k, weight D p m) := (mul_sum ..).symm
         _ ≤ _ := mul_le_mul_of_nonneg_left (weight_partial_le D hp hp' _) (by positivity)

/-- The displayed exact formula has the claimed two-sided growth rate. -/
theorem exactSum_theta (D : ℕ) {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    (fun N => Shell.exactSum D N p) =Θ[atTop] (fun N : ℕ => p⁻¹^N / (N:ℝ)^(D-1)) := by
  let r := D-1
  let B : ℝ := 1 + 3^D * ∑' m, weight D p m
  let C := B * ∑' j, weight r p j
  have bounds (N : ℕ) (hN : 0 < N) :
      (p⁻¹^N / (N:ℝ)^r) / 2^r ≤ Shell.exactSum D N p ∧
      Shell.exactSum D N p ≤ C * (p⁻¹^N / (N:ℝ)^r) :=
    sum_steps_bounds r hp hp' _ B (shell_factor_bounds D hp hp') N hN
  constructor
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨C, eventually_atTop.mpr ⟨1, fun N hN => ?_⟩⟩
    have h := bounds N (by omega)
    rw [Real.norm_eq_abs, abs_of_nonneg ((by positivity : 0 ≤ (p⁻¹^N / (N:ℝ)^r) / 2^r).trans h.1),
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact h.2
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨2^r, eventually_atTop.mpr ⟨1, fun N hN => ?_⟩⟩
    have h := bounds N (by omega)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
      abs_of_nonneg ((by positivity : 0 ≤ (p⁻¹^N / (N:ℝ)^r) / 2^r).trans h.1)]
    simpa only [mul_comm] using (div_le_iff₀ (by positivity : 0 < (2:ℝ)^r)).mp h.1

end Metropolis.Asymptotic
