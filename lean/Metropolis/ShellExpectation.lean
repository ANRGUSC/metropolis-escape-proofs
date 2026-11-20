import Metropolis.ShellAbsorption
import Metropolis.ShellRows

namespace Metropolis.Shell

private noncomputable def incoming (D k : ℕ) (p : ℝ) : ℝ :=
  if k = 0 then 0 else conductance D (k-1) p

/-- Multiply a transient first-step equation by the shell mass to put it
in divergence form. This identity also treats the reflecting origin. -/
private theorem residual {D N k : ℕ} (hD : 0 < D) {p : ℝ} (hp : 0 < p) (hk : k < N)
    (F : ℕ → ℝ) :
    (F k - 1 - killed N (fun j => up D j p) (fun j => down D j p) F k) * mass D k p =
      conductance D k p * (F k - F (k+1)) -
      incoming D k p * (F (k-1) - F k) - mass D k p := by
  simp only [killed, if_pos hk, up, down, incoming]
  split_ifs <;> field_simp [(mass_pos hD k hp).ne'] <;> ring

private theorem potential_equation {D N : ℕ} (hD : 0 < D) {p : ℝ} (hp : 0 < p) (k : ℕ) :
    potential D N p k = (if k < N then 1 else 0) +
      killed N (fun j => up D j p) (fun j => down D j p) (potential D N p) k := by
  by_cases hk : k < N
  · rw [if_pos hk]
    have res := residual hD hp hk (potential D N p)
    rw [potential_drop D N p hk, increment_flux D k hp] at res
    have hz : prefixMass D k p - incoming D k p *
        (potential D N p (k-1) - potential D N p k) - mass D k p = 0 := by
      cases k with
      | zero => simp [prefixMass, mass, shellSize, incoming]
      | succ k =>
        simp only [incoming, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
        rw [potential_drop D N p (by omega), increment_flux D k hp, prefixMass_succ]
        ring
    have eq := (mul_eq_zero.mp (res.trans hz)).resolve_right (mass_pos hD k hp).ne'
    linarith
  · simp [killed, hk, potential, min_eq_right (Nat.le_of_not_gt hk)]

theorem meanTime_summable {D : ℕ} (hD : 0 < D) (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ∀ k, Summable (fun n => survival N (fun j => up D j p) (fun j => down D j p) n k) :=
  (mean_equations (fun k _ => row_probabilities hD hp hp1 k)
    (fun k => sub_nonneg.mpr (exactSum_mono hD hp (min_le_right k N)))
    (potential_equation (N := N) hD hp)).1

/-- Expected time to absorption of the shell-averaged chain from shell zero.
The expectation is the convergent series of its finite-horizon survival probabilities. -/
theorem exact_escape {D : ℕ} (hD : 0 < D) (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    meanTime D N p 0 = exactSum D N p := by
  let T := meanTime D N p
  have eq (k : ℕ) : T k = (if k < N then 1 else 0) +
      killed N (fun j => up D j p) (fun j => down D j p) T k :=
    (mean_equations (fun k _ => row_probabilities hD hp hp1 k)
      (fun k => sub_nonneg.mpr (exactSum_mono hD hp (min_le_right k N)))
      (potential_equation (N := N) hD hp)).2 k
  apply exactSum_of_flux hp T
  · simpa [killed] using eq N
  · intro hn
    have h := residual hD hp hn T
    have e := eq 0
    rw [if_pos hn] at e
    have z : T 0 - 1 - killed N (fun j => up D j p) (fun j => down D j p) T 0 = 0 := by linarith
    rw [z] at h
    simpa [incoming, mass, shellSize] using (show conductance D 0 p * (T 0 - T 1) = 1 by
      simpa [incoming, mass, shellSize] using (sub_eq_zero.mp (by simpa [incoming, mass, shellSize] using h.symm)))
  · intro k hk
    have h := residual hD hp hk T
    have e := eq (k+1)
    rw [if_pos hk] at e
    have z : T (k+1) - 1 - killed N (fun j => up D j p) (fun j => down D j p) T (k+1) = 0 := by
      linarith
    rw [z, zero_mul] at h
    simp only [incoming, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel] at h
    linarith

end Metropolis.Shell
