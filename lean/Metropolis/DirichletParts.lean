import Metropolis.DirichletRows
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace Metropolis.Lattice
open Finset
noncomputable section
variable {D : ℕ}
abbrev Bond (D : ℕ) := Site D × Fin D

def inUnit (h : Site D → ℝ) : Prop := ∀ x, 0 ≤ h x ∧ h x ≤ 1

theorem diff_le_one {h : Site D → ℝ} (hb : inUnit h) (x y : Site D) :
    |h x-h y| ≤ 1 := by
  rw [abs_le]
  have hx := hb x
  have hy := hb y
  constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]

def rightShift : Bond D ≃ Bond D where
  toFun e := (step e.1 e.2 1,e.2)
  invFun e := (step e.1 e.2 (-1),e.2)
  left_inv := fun ⟨x,i⟩ => by simp [step_cancel]
  right_inv := fun ⟨x,i⟩ => Prod.ext (step_cancel x i (-1)) rfl

theorem summable_weight {p : ℝ} (hp : 0 < p) (hm : Summable (mass (D:=D) p)) :
    Summable (fun e : Bond D => mass p e.1) := by
  apply (summable_prod_of_nonneg (f := fun e : Bond D => mass p e.1) (fun e => (mass_pos p hp e.1).le)).2
  refine ⟨fun x => Summable.of_finite, ?_⟩
  simpa [tsum_fintype] using (hm.mul_left (D:ℝ))

theorem conductance_le_mass {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (x : Site D) (i : Fin D) :
    conductance p x i ≤ mass p x := by
  have hd : 1 ≤ (D:ℝ) := by exact_mod_cast (show 1 ≤ D by have := i.isLt; omega)
  calc conductance p x i ≤ p ^ max (level x) (level (step x i 1)) :=
         div_le_self (by positivity) (by linarith)
       _ ≤ _ := pow_le_pow_of_le_one hp.le hp1 (le_max_left _ _)

private def leftTerm (p : ℝ) (h g : Site D → ℝ) (e : Bond D) :=
  currentDiff p h e.1 e.2 * g e.1
private def rightTerm (p : ℝ) (h g : Site D → ℝ) (e : Bond D) :=
  currentDiff p h e.1 e.2 * g (step e.1 e.2 1)

def mixed (p : ℝ) (h g : Site D → ℝ) (e : Bond D) : ℝ :=
  currentDiff p h e.1 e.2 * (g e.1 - g (step e.1 e.2 1))

private theorem weighted_bound {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    {h g : Site D → ℝ} (hb : inUnit h) (gb : inUnit g) (x y : Site D) (i : Fin D) :
    ‖currentDiff p h x i * g y‖ ≤ mass p x := by
  simp only [Real.norm_eq_abs, currentDiff, abs_mul, abs_of_nonneg (conductance_pos p hp x i).le,
    abs_of_nonneg (gb y).1]
  have hle := mul_le_mul (mul_le_mul_of_nonneg_left (diff_le_one hb x (step x i 1))
    (conductance_pos p hp x i).le) (gb y).2 (gb y).1
      (mul_nonneg (conductance_pos p hp x i).le zero_le_one)
  exact (by simpa using hle : conductance p x i * |h x-h (step x i 1)| * g y ≤ conductance p x i).trans
    (conductance_le_mass hp hp1 x i)

theorem summable_mixed {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hm : Summable (mass (D:=D) p))
    {h g : Site D → ℝ} (hb : inUnit h) (gb : inUnit g) :
    Summable (mixed p h g) := by
  have L : Summable (leftTerm p h g) := (summable_weight hp hm).of_norm_bounded
    (fun e => weighted_bound hp hp1 hb gb _ _ _)
  have R : Summable (rightTerm p h g) := (summable_weight hp hm).of_norm_bounded
    (fun e => weighted_bound hp hp1 hb gb _ _ _)
  exact (L.sub R).congr (fun e => by simp [mixed,leftTerm,rightTerm,mul_sub])

/-- Green's summation-by-parts identity on the infinite lattice. Translation by
one step converts right endpoints of positive edges into left endpoints of negative ones. -/
theorem integration_by_parts {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hm : Summable (mass (D:=D) p))
    {h g : Site D → ℝ} (hb : inUnit h) (gb : inUnit g) :
    ∑' e : Bond D, mixed p h g e = ∑' x : Site D, (mass p x * (h x-edgeRowMean p h x)) * g x := by
  have L : Summable (leftTerm p h g) := (summable_weight hp hm).of_norm_bounded
    (fun e => weighted_bound hp hp1 hb gb _ _ _)
  have R : Summable (rightTerm p h g) := (summable_weight hp hm).of_norm_bounded
    (fun e => weighted_bound hp hp1 hb gb _ _ _)
  let B : Bond D → ℝ := fun e => rightTerm p h g (rightShift.symm e)
  have hsB : Summable B := (rightShift.symm.summable_iff).2 R
  calc _ = (∑' e, leftTerm p h g e) - ∑' e, rightTerm p h g e := by
             rw [← L.tsum_sub R]
             apply tsum_congr; intro e; simp [mixed,leftTerm,rightTerm,mul_sub]
       _ = (∑' e, leftTerm p h g e) - ∑' e, B e := by
             have shiftSum : (∑' e : Bond D, B e) = ∑' e, rightTerm p h g e :=
               (@rightShift D).symm.tsum_eq (rightTerm p h g)
             rw [shiftSum]
       _ = ∑' e : Bond D, (leftTerm p h g e-B e) := (L.tsum_sub hsB).symm
       _ = ∑' x : Site D, ∑' i : Fin D, (leftTerm p h g (x,i)-B (x,i)) :=
             (L.sub hsB).tsum_prod' (fun _ => Summable.of_finite)
       _ = _ := by
             apply tsum_congr
             intro x
             rw [tsum_fintype, residual_as_edges hp, Finset.sum_mul]
             apply Finset.sum_congr rfl
             intro i _
             have cancel : step (step x i (-1)) i 1 = x := step_cancel x i (-1)
             simp [leftTerm, B, rightTerm, rightShift, cancel, sub_mul]

end
end Metropolis.Lattice
