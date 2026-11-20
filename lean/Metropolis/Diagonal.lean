import Metropolis.EscapeGap
import Mathlib.Tactic.FieldSimp

open scoped ENNReal
noncomputable section
namespace Metropolis.Lattice
variable {D : ℕ}

/-- The mean number of visits to a before absorption, including time zero. -/
theorem diagonal_visits {p : ℝ} (hD : 0 < D) (hp : 0 < p) (hp1 : p ≤ 1)
    {A : Set (Site D)} {a : Site D} (ha : a ∉ A) (hA : A.Nonempty) :
    Green.occupation (stopped p A) a a = ENNReal.ofReal ((1-rowMean p (hit p a A) a)⁻¹) := by
  let K := stopped p A
  let t := rowMean p (hit p a A) a
  let g := Green.occupation K a a
  have tpos : 0 ≤ t := Finset.sum_nonneg fun y _ => mul_nonneg
    (prob_nonneg hD hp hp1 a y) (hit_bounds hD hp hp1 A a y).1
  have tlt : t < 1 := first_return_lt_one hD hp hp1 ha hA
  have d : 0 < 1-t := sub_pos.mpr tlt
  let B := (1-t)⁻¹
  have bpos : 0 < B := inv_pos.mpr d
  have bfix : 1+t*B=B := by dsimp [B]; field_simp [d.ne']; ring
  have row : (∑' y, K a y * Green.entrance K a y) = ENNReal.ofReal t :=
    stopped_row_entrance hD hp hp1 ha ha
  have hB : 1 + (∑' y, K a y * Green.entrance K a y) * ENNReal.ofReal B ≤ ENNReal.ofReal B := by
    rw [row, ← ENNReal.ofReal_mul tpos, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (mul_nonneg tpos bpos.le), bfix]
  have hg : g ≠ ∞ := by
    have bound := Green.occupation_majorant (ENNReal.ofReal B) hB a
    simp only [Green.entrance_at, one_mul] at bound
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top bound
  have eq : g = 1 + ENNReal.ofReal t * g := by
    calc g = Green.identity a a + ∑' y, K a y * Green.occupation K y a := Green.occupation_equation K a a
         _ = 1 + (∑' y, K a y * Green.entrance K a y) * g := by
           simp only [Green.identity, ← ENNReal.tsum_mul_right]
           congr 1; apply tsum_congr; intro y
           rw [Green.occupation_first K a y, mul_assoc]
         _ = _ := by rw [row]
  have er := congrArg ENNReal.toReal eq
  rw [ENNReal.toReal_add ENNReal.one_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg),
      ENNReal.toReal_one, ENNReal.toReal_mul, ENNReal.toReal_ofReal tpos] at er
  have realEq : g.toReal = B := by
    apply (mul_right_cancel₀ d.ne')
    calc g.toReal * (1-t) = 1 := by linarith
         _ = B * (1-t) := (inv_mul_cancel₀ d.ne').symm
  change g = ENNReal.ofReal B
  rw [← realEq, ENNReal.ofReal_toReal hg]
end Metropolis.Lattice
end
