import Metropolis.HittingStatement

open scoped ENNReal
noncomputable section
namespace Metropolis.Lattice
variable {D : ℕ}

/-- Assemble the reversible Green identity and the equilibrium-capacity computation
without dividing by a possibly infinite occupation time. -/
theorem hitting_from_capacity {p : ℝ} (hD : 0 < D) (hp : 0 < p) (hp1 : p < 1)
    {A : Set (Site D)} {a : Site D} (ha : a ∉ A)
    (gap : rowMean p (hit p a A) a < 1)
    (visits : Green.occupation (stopped p A) a a =
      ENNReal.ofReal ((1 - rowMean p (hit p a A) a)⁻¹))
    (cap : capacity p a A = ENNReal.ofReal (mass p a * (1 - rowMean p (hit p a A) a))) :
    meanHitting p a A ≠ ∞ ∧
    meanHitting p a A = (capacity p a A)⁻¹ *
      (∑' x, ENNReal.ofReal (mass p x) * Green.entrance (stopped p A) a x) ∧
    ENNReal.ofReal (mass p a) * (capacity p a A)⁻¹ ≤ meanHitting p a A ∧
    meanHitting p a A ≤ (∑' x : Site D, ENNReal.ofReal (mass p x)) * (capacity p a A)⁻¹ := by
  classical
  let K := stopped p A
  let μ := fun x : Site D => ENNReal.ofReal (mass p x)
  let S := ∑' x, μ x * Green.entrance K a x
  let q := 1 - rowMean p (hit p a A) a
  have hq : 0 < q := sub_pos.mpr gap
  have hm := mass_pos p hp a
  have cap0 : capacity p a A ≠ 0 := by rw [cap]; exact (ENNReal.ofReal_pos.mpr (mul_pos hm hq)).ne'
  have captop : capacity p a A ≠ ∞ := by rw [cap]; exact ENNReal.ofReal_ne_top
  have rev : Green.Balance μ K := Green.killed_balance (transition_balance hp) A
  have w := Green.weighted_lifetime rev a
  have diag : Green.occupation K a a * ENNReal.ofReal q = 1 := by
    change Green.occupation (stopped p A) a a * ENNReal.ofReal q = 1
    rw [visits, ← ENNReal.ofReal_mul (inv_pos.mpr hq).le]
    change ENNReal.ofReal (q⁻¹ * q) = 1
    rw [inv_mul_cancel₀ hq.ne', ENNReal.ofReal_one]
  have wl : capacity p a A * meanHitting p a A = S := by
    rw [cap, ENNReal.ofReal_mul hm.le]
    simp only [meanHitting, if_neg ha]
    change (μ a * ENNReal.ofReal q) * Green.meanLifetime K a = S
    calc _ = (μ a * Green.meanLifetime K a) * ENNReal.ofReal q := by ac_rfl
         _ = (S * Green.occupation K a a) * ENNReal.ofReal q := by rw [w]
         _ = S := by rw [mul_assoc, diag, mul_one]
  have formula : meanHitting p a A = (capacity p a A)⁻¹ * S := by
    rw [← wl, ENNReal.inv_mul_cancel_left cap0 captop]
  have lower : μ a ≤ S := by
    have e := ENNReal.sum_le_tsum (f:=fun x => μ x * Green.entrance K a x) ({a} : Finset _)
    simpa [S, Green.entrance_at] using e
  have upper : S ≤ ∑' x, μ x := by
    apply ENNReal.tsum_le_tsum; intro x
    have b := Green.entrance_le_one (stopped_substochastic hD hp hp1.le A) a x
    calc _ ≤ μ x * 1 := by gcongr
         _ = μ x := mul_one _
  have Sfinite := ne_top_of_le_ne_top (total_mass_ne_top hp hp1) upper
  refine ⟨?_, formula, ?_, ?_⟩
  · rw [formula]; exact ENNReal.mul_ne_top (by simpa using cap0) Sfinite
  · rw [formula, mul_comm]; gcongr
  · rw [formula, mul_comm]; gcongr
end Metropolis.Lattice
end
