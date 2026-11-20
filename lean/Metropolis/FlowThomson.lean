import Metropolis.FlowResistance
import Metropolis.Capacity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

noncomputable section
open scoped ENNReal
namespace Metropolis.Flow
open Metropolis.Lattice

/-- Weak Thomson inequality on the full lattice: pairing any unit flow with
each admissible Dirichlet potential and applying weighted Cauchy--Schwarz. -/
theorem weak_thomson {D : ℕ} {p : ℝ} (hp : 0 < p) (A : Set (Site D))
    (b : Batch D) (hb : unitTo A b) :
    (capacity p 0 A)⁻¹ ≤ ENNReal.ofReal (energy p b) := by
  classical
  suffices main : (ENNReal.ofReal (energy p b))⁻¹ ≤ capacity p 0 A by
    simpa using ENNReal.inv_le_inv.mpr main
  unfold capacity
  refine le_iInf fun f => le_iInf fun h0 => le_iInf fun hA => ?_
  let c : Site D × Fin D → ℝ := fun e => conductance p e.1 e.2
  let grad : Site D × Fin D → ℝ := fun e => f e.1 - f (step e.1 e.2 1)
  let term : Site D × Fin D → ℝ := fun e => c e * grad e ^ 2
  have hc (e) : 0 < c e := conductance_pos p hp _ _
  have ht (e) : 0 ≤ term e := mul_nonneg (hc e).le (sq_nonneg _)
  have hpair : ∑ j, b.current j * grad (b.key j) = 1 := (hb f hA).trans h0
  have cs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (R:=ℝ) Finset.univ
    (r:=fun j => b.current j * grad (b.key j))
    (f:=fun j => b.current j ^ 2 / c (b.key j))
    (g:=fun j => term (b.key j))
    (fun j _ => div_nonneg (sq_nonneg _) (hc _).le)
    (fun j _ => ht _)
    (fun j _ => by unfold term; rw [mul_pow]; field_simp [ne_of_gt (hc (b.key j))] <;> exact le_rfl)
  rw [hpair,one_pow] at cs
  change 1 ≤ energy p b * ∑ j, term (b.key j) at cs
  have henergy : 0 ≤ energy p b :=
    Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (hc _).le
  have hpos : 0 < energy p b := lt_of_le_of_ne henergy (fun he => by rw [← he,zero_mul] at cs; norm_num at cs)
  have htest : (energy p b)⁻¹ ≤ ∑ j, term (b.key j) := by
    rw [inv_eq_one_div,div_le_iff₀ hpos,mul_comm]; exact cs
  rw [← ENNReal.ofReal_inv_of_pos hpos]
  calc
    _ ≤ ENNReal.ofReal (∑ j, term (b.key j)) := ENNReal.ofReal_le_ofReal htest
    _ = ∑ j, ENNReal.ofReal (term (b.key j)) := ENNReal.ofReal_sum_of_nonneg (fun _ _ => ht _)
    _ = ∑ e ∈ Finset.univ.image b.key, ENNReal.ofReal (term e) :=
      (Finset.sum_image (s:=Finset.univ) (f:=fun e => ENNReal.ofReal (term e))
        (fun i _ j _ hij => b.distinct hij)).symm
    _ ≤ ∑' e, ENNReal.ofReal (term e) := ENNReal.sum_le_tsum _
    _ = _ := rfl

end Metropolis.Flow
