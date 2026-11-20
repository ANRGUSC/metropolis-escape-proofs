import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

open scoped BigOperators
open Finset Filter

namespace Metropolis.Asymptotic

/-- A summable majorant for the backward tail of the shell-increment sum. -/
def weight (r : ℕ) (p : ℝ) (n : ℕ) : ℝ := ((n:ℝ)+1)^r * p^n

theorem weight_summable (r : ℕ) {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    Summable (weight r p) := by
  have h := summable_pow_mul_geometric_of_norm_lt_one r
    (show ‖p‖ < 1 by rwa [Real.norm_eq_abs, abs_of_pos hp])
  have hs := (summable_nat_add_iff 1).2 h
  refine (hs.mul_right p⁻¹).congr fun n => ?_
  simp [weight, pow_succ, mul_assoc, hp.ne']

theorem weight_partial_le (r : ℕ) {p : ℝ} (hp : 0 < p) (hp' : p < 1) (n : ℕ) :
    ∑ j ∈ range n, weight r p j ≤ ∑' j, weight r p j := by
  exact (weight_summable r hp hp').sum_le_tsum _ (fun j _ => by unfold weight; positivity)

/-- Compare a summand with the scale at the endpoint, losing only a summable weight
in the distance from the endpoint. -/
theorem step_le_endpoint (r k j : ℕ) {p : ℝ} (hp : 0 < p) :
    p⁻¹^(k+1) / (2*(k:ℝ)+1)^r ≤
      (p⁻¹^(k+1+j) / ((k+1+j : ℕ):ℝ)^r) * weight r p j := by
  have ha : 0 < 2*(k:ℝ)+1 := by positivity
  have hn : 0 < ((k+1+j : ℕ):ℝ) := by positivity
  have hsize : ((k+1+j : ℕ):ℝ) ≤ (2*(k:ℝ)+1) * ((j:ℝ)+1) := by
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (Nat.cast_nonneg (α := ℝ) j)]
  have hs := pow_le_pow_left₀ hn.le hsize r
  rw [mul_pow] at hs
  unfold weight
  rw [pow_add p⁻¹ (k+1) j, inv_pow p j]
  have he : p⁻¹^(k+1) * (p^j)⁻¹ / ((k+1+j : ℕ):ℝ)^r * (((j:ℝ)+1)^r * p^j) =
      p⁻¹^(k+1) * ((j:ℝ)+1)^r / ((k+1+j : ℕ):ℝ)^r := by
    field_simp [hp.ne']
  rw [he, div_le_div_iff₀ (pow_pos ha _) (pow_pos hn _)]
  calc _ ≤ p⁻¹^(k+1) * ((2*(k:ℝ)+1)^r * ((j:ℝ)+1)^r) := by gcongr
       _ = _ := by ring

/-- Summing all shell increments preserves the endpoint scale. -/
theorem sum_steps_bounds (r : ℕ) {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (F : ℕ → ℝ) (B : ℝ) (hF : ∀ k, 1 ≤ F k ∧ F k ≤ B) (N : ℕ) (hN : 0 < N) :
    (p⁻¹^N / (N:ℝ)^r) / 2^r ≤
      ∑ k ∈ range N, p⁻¹^(k+1) / (2*(k:ℝ)+1)^r * F k ∧
    (∑ k ∈ range N, p⁻¹^(k+1) / (2*(k:ℝ)+1)^r * F k) ≤
      (B * ∑' j, weight r p j) * (p⁻¹^N / (N:ℝ)^r) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  have hB : 0 ≤ B := le_trans (by norm_num : (0:ℝ) ≤ 1) ((hF 0).1.trans (hF 0).2)
  let scale := p⁻¹^(n+1) / ((n+1:ℕ):ℝ)^r
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  constructor
  · apply le_trans _ (single_le_sum (f := fun k : ℕ => p⁻¹^(k+1) / (2*(k:ℝ)+1)^r * F k)
        (fun i _ => mul_nonneg (by positivity) (by linarith [(hF i).1])) (self_mem_range_succ n))
    have hden : (2*(n:ℝ)+1)^r ≤ 2^r * ((n+1:ℕ):ℝ)^r := by
      rw [← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      push_cast
      linarith
    calc (p⁻¹^(n+1) / ((n+1:ℕ):ℝ)^r) / 2^r =
          p⁻¹^(n+1) / (2^r * ((n+1:ℕ):ℝ)^r) := by ring
         _ ≤ p⁻¹^(n+1) / (2*(n:ℝ)+1)^r := by gcongr
         _ ≤ _ := le_mul_of_one_le_right (by positivity) (hF n).1
  · have hu (k : ℕ) (hk : k ∈ range (n+1)) :
        p⁻¹^(k+1) / (2*(k:ℝ)+1)^r * F k ≤ scale * B * weight r p (n-k) := by
      have hkj : k+1+(n-k) = n+1 := by have := mem_range.mp hk; omega
      have h := step_le_endpoint r k (n-k) hp
      rw [hkj] at h
      calc _ ≤ (scale * weight r p (n-k)) * B :=
               mul_le_mul h (hF k).2 (by linarith [(hF k).1]) (by unfold scale weight; positivity)
           _ = _ := by ring
    calc _ ≤ ∑ k ∈ range (n+1), scale * B * weight r p (n-k) := sum_le_sum hu
         _ = (scale*B) * (∑ j ∈ range (n+1), weight r p j) := by
           rw [← mul_sum]
           congr 1
           simpa using sum_range_reflect (weight r p) (n+1)
         _ ≤ (scale*B) * (∑' j, weight r p j) :=
           mul_le_mul_of_nonneg_left (weight_partial_le r hp hp' _) (mul_nonneg hscale hB)
         _ = _ := by
           change (scale * B) * (∑' j, weight r p j) = (B * ∑' j, weight r p j) * scale
           ring

end Metropolis.Asymptotic
