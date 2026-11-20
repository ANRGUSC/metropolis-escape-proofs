import Metropolis.LowerCut
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped ENNReal

namespace Metropolis.Lower
open Metropolis.Lattice

theorem scale_le_inverse_cut (d k : ℕ) {p : ℝ} (hp : 0 < p) :
    (1 / (2:ℝ)^d) * ((1/p)^(k+1) / ((k:ℝ)+1)^d) ≤
      (p^(k+1) * (2*(k:ℝ)+1)^d)⁻¹ := by
  have hbase : 2*(k:ℝ)+1 ≤ 2*((k:ℝ)+1) := by linarith
  have hpow := pow_le_pow_left₀ (by positivity) hbase d
  rw [mul_pow] at hpow
  have h := one_div_le_one_div_of_le (by positivity) hpow
  simp only [one_div, mul_inv_rev] at h
  simp only [one_div, inv_pow, div_eq_mul_inv, mul_inv_rev]
  calc _ = (((k:ℝ)+1)^d)⁻¹ * ((2:ℝ)^d)⁻¹ * (p^(k+1))⁻¹ := by ring
       _ ≤ ((2*(k:ℝ)+1)^d)⁻¹ * (p^(k+1))⁻¹ :=
         mul_le_mul_of_nonneg_right h (by positivity)
       _ = _ := by ring

/-- Resistance of the original network is bounded below by the inverse
conductance of its last cut. This is the explicit constant from Theorem 3. -/
theorem resistance_lower {D N : ℕ} (hD : 0 < D) (hN : 0 < N) {p : ℝ}
    (hp : 0 < p) (hp' : p ≤ 1) :
    ENNReal.ofReal ((1 / (2:ℝ)^(D-1)) * ((1/p)^N / (N:ℝ)^(D-1))) ≤
      (capacity p (0 : Site D) {x | level x = N})⁻¹ := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have hC := capacity_last_cut d k hp hp'
  apply le_trans _ (ENNReal.inv_le_inv.mpr hC)
  rw [← ENNReal.ofReal_inv_of_pos (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  simpa only [Nat.succ_sub_one,Nat.cast_succ] using scale_le_inverse_cut d k hp

end Metropolis.Lower
