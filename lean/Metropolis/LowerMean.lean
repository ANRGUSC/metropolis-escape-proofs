import Metropolis.LowerStatement
import Metropolis.LowerResistance
import Metropolis.LowerSurvival

open scoped ENNReal
namespace Metropolis.Lower
open Metropolis.Lattice Metropolis.Green

/-- The actual stopped lattice kernel can lose at most the stationary flux of
the last cut at each time. Summing the first half of the resulting triangular
survival bound proves the claimed uniform lower estimate. -/
theorem lower_from_cut_flux
    (cut : ∀ (d k : ℕ) {p : ℝ}, 0 < p → p < 1 →
      stationaryExit (transition p) (fun x : Site (d+1) => ENNReal.ofReal (mass p x))
          {x | ¬level x ≤ k} ≤ ENNReal.ofReal (p^(k+1)*(2*(k:ℝ)+1)^d)) :
    EscapeLowerStatement := by
  classical
  intro D hD p hp hp'
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : D ≠ 0)
  refine ⟨(1/4)*(1/(2:ℝ)^d), by positivity, ?_⟩
  intro N hN
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  let P : Kernel (Site (d+1)) := transition p
  let μ : Site (d+1) → ℝ≥0∞ := fun x => ENNReal.ofReal (mass p x)
  let A : Set (Site (d+1)) := {x | level x = k+1}
  let B : Set (Site (d+1)) := {x | ¬level x ≤ k}
  let u := stay (killed P B) (0 : Site (d+1))
  let b := p^(k+1)*(2*(k:ℝ)+1)^d
  have hb : 0 < b := by unfold b; positivity
  have flux_le : stationaryExit P μ B ≤ ENNReal.ofReal b :=
    cut d k hp hp'
  have hP := transition_stochastic (D:=d+1) (by omega) hp hp'.le
  have u_le (n : ℕ) : u n ≤ 1 :=
    stay_le_one _ (fun x => (ENNReal.tsum_le_tsum (killed_le P B x)).trans (hP x).le) _ n
  have survive (n : ℕ) : 1 ≤ u n + n * ENNReal.ofReal b := by
    apply (stay_plus_flux P μ hP (transition_balance hp) B 0 (by simp [B]) (by simp [μ]) n).trans
    exact add_le_add le_rfl (mul_le_mul' le_rfl flux_le)
  have comparison : (∑' n, u n) ≤ meanHitting p (0 : Site (d+1)) A := by
    have hA : (0 : Site (d+1)) ∉ A := by simp [A]
    letI : DecidablePred (· ∈ A) := fun _ => Classical.propDecidable _
    simp only [meanHitting, if_neg hA]
    apply killed_mean_mono P (a:=0)
    intro x hx
    change level x = k+1 at hx
    change ¬level x ≤ k
    omega
  apply le_trans _ ((quarter_flux u b hb u_le survive).trans comparison)
  apply ENNReal.ofReal_le_ofReal
  simp only [Nat.succ_sub_one, Nat.cast_succ, Nat.succ_eq_add_one]
  calc _ = (1/4)*((1/(2:ℝ)^d) * ((1/p)^(k+1)/((k:ℝ)+1)^d)) := by ring
       _ ≤ (1/4)*(p^(k+1)*(2*(k:ℝ)+1)^d)⁻¹ :=
         mul_le_mul_of_nonneg_left (scale_le_inverse_cut d k hp) (by norm_num)
       _ = 1/(4*b) := by unfold b; ring

end Metropolis.Lower
