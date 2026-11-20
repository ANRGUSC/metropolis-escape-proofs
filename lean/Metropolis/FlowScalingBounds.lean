import Metropolis.FlowScalingStatement
import Mathlib.Tactic.Positivity

open Filter
open scoped ENNReal Asymptotics
namespace Metropolis.Flow

theorem theta_of_enclosure (h : ℕ → ℝ≥0∞) (s : ℕ → ℝ) (hs : ∀ N, 0 ≤ s N)
    {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (lower : ∀ N : ℕ, 1 ≤ N → ENNReal.ofReal (c*s N) ≤ h N)
    (upper : ∀ N : ℕ, 1 ≤ N → h N ≤ ENNReal.ofReal (C*s N)) :
    (∀ N : ℕ, 1 ≤ N → h N ≠ ∞) ∧
    (fun N : ℕ => (h N).toReal) =Θ[atTop] s := by
  have finite (N) (hN : 1 ≤ N) : h N ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (upper N hN)
  refine ⟨finite,?_,?_⟩
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨C,eventually_atTop.mpr ⟨1,fun N hN => ?_⟩⟩
    rw [Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg,Real.norm_eq_abs,abs_of_nonneg (hs _)]
    have u := ENNReal.toReal_mono ENNReal.ofReal_ne_top (upper N hN)
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hC (hs N))] using u
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨c⁻¹,eventually_atTop.mpr ⟨1,fun N hN => ?_⟩⟩
    rw [Real.norm_eq_abs,abs_of_nonneg (hs _),Real.norm_eq_abs,abs_of_nonneg ENNReal.toReal_nonneg]
    have l := ENNReal.toReal_mono (finite N hN) (lower N hN)
    rw [ENNReal.toReal_ofReal (mul_nonneg hc.le (hs _))] at l
    rw [inv_mul_eq_div,le_div_iff₀ hc,mul_comm]
    exact l

end Metropolis.Flow
