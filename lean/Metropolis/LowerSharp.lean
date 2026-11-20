import Metropolis.Hitting
import Metropolis.LowerResistance
import Metropolis.FlowShell

open scoped ENNReal

namespace Metropolis.Lower
open Metropolis.Lattice

private theorem resistance_le_shell_mean (d k : ℕ) {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    (capacity p (0 : Site (d+1)) {x | level x = k+1})⁻¹ ≤
      meanHitting p (0 : Site (d+1)) {x | level x = k+1} := by
  let A : Set (Site (d+1)) := {x | level x = k+1}
  have hA : (0 : Site (d+1)) ∉ A := by simp [A]
  simpa [A] using (hitting_capacity (d+1) (by omega) p hp hp' 0 A
    (Flow.nonempty_shell d (k+1)) (Flow.finite_shell _ _) hA).2.2.2.1

/-- The inverse conductance of the last cut bounds the actual mean escape
time from below at each positive depth. -/
theorem escape_last_cut (d k : ℕ) {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    ENNReal.ofReal ((1/p)^(k+1) / (2*(k:ℝ)+1)^d) ≤
      meanHitting p (0 : Site (d+1)) {x | level x = k+1} := by
  have hcut := capacity_last_cut d k hp hp'.le
  have hres := ENNReal.inv_le_inv.mpr hcut
  rw [← ENNReal.ofReal_inv_of_pos (by positivity)] at hres
  calc _ = ENNReal.ofReal (p^(k+1) * (2*(k:ℝ)+1)^d)⁻¹ := by
          congr 1
          simp [one_div, inv_pow, div_eq_mul_inv, mul_comm]
       _ ≤ _ := hres.trans (resistance_le_shell_mean d k hp hp')

/-- The explicit uniform constant in the paper: one can take c=2^{-(D-1)}
for every positive dimension and basin depth. -/
theorem escape_lower_sharp {D N : ℕ} (hD : 0 < D) (hN : 0 < N) {p : ℝ}
    (hp : 0 < p) (hp' : p < 1) :
    ENNReal.ofReal ((1 / (2:ℝ)^(D-1)) * ((1/p)^N / (N:ℝ)^(D-1))) ≤
      meanHitting p (0 : Site D) {x | level x = N} := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  exact (resistance_lower hD hN hp hp'.le).trans (resistance_le_shell_mean d k hp hp')

#print axioms escape_last_cut
#print axioms escape_lower_sharp
end Metropolis.Lower
