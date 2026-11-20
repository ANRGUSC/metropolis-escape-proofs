import Metropolis.Renewal

open scoped ENNReal
open Finset
namespace Metropolis.Green
noncomputable section
variable {S : Type*} [DecidableEq S]

theorem entrance_at (P : Kernel S) (a : S) : entrance P a a = 1 := by
  unfold entrance
  rw [tsum_eq_zero_add' ENNReal.summable]
  simp [first, identity]

theorem entrance_away (P : Kernel S) (a x : S) (hx : x ≠ a) :
    entrance P a x = ∑' y, P x y * entrance P a y := by
  unfold entrance
  rw [tsum_eq_zero_add' (f:=fun n => first P a n x) ENNReal.summable]
  simp only [first, identity, if_neg hx, zero_add, ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_comm

theorem occupation_equation (P : Kernel S) (a x : S) :
    occupation P x a = identity x a + ∑' y, P x y * occupation P y a := by
  unfold occupation
  rw [tsum_eq_zero_add' (f:=fun n => steps P n x a) ENNReal.summable]
  simp only [steps, compose, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm (f:=fun n y => P x y * steps P n y a)]

/-- Occupation is the least nonnegative solution of the Green majorant inequality. -/
theorem occupation_le {P : Kernel S} {a : S} (v : S → ℝ≥0∞)
    (hv : ∀ x, identity x a + ∑' y, P x y * v y ≤ v x) (x : S) :
    occupation P x a ≤ v x := by
  have partial_bound (n : ℕ) (w : S) : ∑ t ∈ range n, steps P t w a ≤ v w := by
    induction n generalizing w with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ']
      simp only [steps, compose]
      rw [← sum_interchange]
      calc
        _ = identity w a + ∑' y, P w y * ∑ t ∈ range n, steps P t y a := by
          simp only [Finset.mul_sum, add_comm]
        _ ≤ identity w a + ∑' y, P w y * v y := by
          gcongr with y; exact ih y
        _ ≤ _ := hv w
  unfold occupation
  rw [ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun n => partial_bound n x

/-- Expected time is the total reversible mass weighted by the first-hit probability,
in units of the mean number of visits to the source. -/
theorem weighted_lifetime {P : Kernel S} {μ : S → ℝ≥0∞} (rev : Balance μ P) (a : S) :
    μ a * meanLifetime P a =
      (∑' x, μ x * entrance P a x) * occupation P a a := by
  rw [meanLifetime_eq_total_occupation, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  apply tsum_congr; intro x
  rw [occupation_balance rev a x, occupation_first P a x, mul_assoc]

/-- A strict chance of absorption before the next return bounds all occupation counts. -/
theorem occupation_majorant {P : Kernel S} {a : S} (B : ℝ≥0∞)
    (hB : 1 + (∑' y, P a y * entrance P a y) * B ≤ B) (x : S) :
    occupation P x a ≤ entrance P a x * B := by
  apply occupation_le
  intro w
  simp_rw [← mul_assoc, ENNReal.tsum_mul_right]
  by_cases e : w = a
  · subst w; simpa [identity, entrance_at] using hB
  · simp [identity, e, ← entrance_away P a w e]

end
end Metropolis.Green
