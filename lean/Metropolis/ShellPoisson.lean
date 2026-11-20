import Metropolis.Shell
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Metropolis.Shell

def area (D k : ℕ) : ℝ := (2*(k:ℝ)+1)^(D-1)
noncomputable def mass (D k : ℕ) (p : ℝ) : ℝ := shellSize D k * p^k
noncomputable def conductance (D k : ℕ) (p : ℝ) : ℝ := p^(k+1) * area D k
noncomputable def prefixMass (D k : ℕ) (p : ℝ) : ℝ :=
  1 + ∑ m ∈ Finset.range k, shellSize D (m+1) * p^(m+1)
noncomputable def increment (D k : ℕ) (p : ℝ) : ℝ :=
  p⁻¹ ^ (k+1) / area D k * prefixMass D k p

theorem area_pos (D k : ℕ) : 0 < area D k := by unfold area; positivity

theorem shellSize_pos {D : ℕ} (hD : 0 < D) (k : ℕ) : 0 < shellSize D k := by
  cases k with
  | zero => simp [shellSize]
  | succ k =>
    simp only [shellSize, Nat.succ_ne_zero, if_false, Nat.cast_succ]
    apply sub_pos.mpr
    apply pow_lt_pow_left₀ <;> first | positivity | linarith | omega

theorem mass_pos {D : ℕ} (hD : 0 < D) (k : ℕ) {p : ℝ} (hp : 0 < p) :
    0 < mass D k p := mul_pos (shellSize_pos hD k) (pow_pos hp _)

theorem conductance_pos (D k : ℕ) {p : ℝ} (hp : 0 < p) :
    0 < conductance D k p := mul_pos (pow_pos hp _) (area_pos D k)

theorem increment_flux (D k : ℕ) {p : ℝ} (hp : 0 < p) :
    conductance D k p * increment D k p = prefixMass D k p := by
  unfold conductance increment
  rw [inv_pow]
  field_simp [hp.ne', (area_pos D k).ne']

theorem prefixMass_succ (D k : ℕ) (p : ℝ) :
    prefixMass D (k+1) p = prefixMass D k p + mass D (k+1) p := by
  simp [prefixMass, Finset.sum_range_succ, mass, add_assoc]

/-- The only solution of the weighted first-step equations at the origin is the
paper's finite sum. The last equation is the absorbing boundary condition. -/
theorem exactSum_of_flux {D N : ℕ} {p : ℝ} (hp : 0 < p) (T : ℕ → ℝ)
    (terminal : T N = 0)
    (base : 0 < N → conductance D 0 p * (T 0 - T 1) = 1)
    (step : ∀ k, k+1 < N →
      conductance D (k+1) p * (T (k+1) - T (k+2)) =
      conductance D k p * (T k - T (k+1)) + mass D (k+1) p) :
    T 0 = exactSum D N p := by
  have flux (k : ℕ) (hk : k < N) :
      conductance D k p * (T k - T (k+1)) = prefixMass D k p := by
    induction k with
    | zero => simpa [prefixMass] using base hk
    | succ k ih => rw [step k hk, ih (by omega), prefixMass_succ]
  have telescopes (n : ℕ) (hn : n ≤ N) :
      ∑ k ∈ Finset.range n, increment D k p = T 0 - T n := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih (by omega)]
      have heq : T n - T (n+1) = increment D n p :=
        mul_left_cancel₀ (conductance_pos D n hp).ne'
          ((flux n (by omega)).trans (increment_flux D n hp).symm)
      linarith
  simpa [exactSum, increment, prefixMass, area, terminal] using (telescopes N le_rfl).symm

/-- Row probabilities of the weighted quotient formed from the shell masses
and face conductances. At zero the chain has no inward edge. -/
noncomputable def up (D k : ℕ) (p : ℝ) : ℝ := conductance D k p / mass D k p
noncomputable def down (D : ℕ) (k : ℕ) (p : ℝ) : ℝ :=
  if k = 0 then 0 else conductance D (k-1) p / mass D k p

theorem up_eq {D : ℕ} (hD : 0 < D) (k : ℕ) {p : ℝ} (hp : 0 < p) :
    up D k p = p * area D k / shellSize D k := by
  unfold up conductance mass
  rw [pow_succ]
  field_simp [hp.ne', (shellSize_pos hD k).ne']

theorem up_zero (D : ℕ) (p : ℝ) : up D 0 p = p := by
  simp [up, mass, conductance, area, shellSize]

theorem down_succ {D : ℕ} (hD : 0 < D) (k : ℕ) {p : ℝ} (hp : 0 < p) :
    down D (k+1) p = area D k / shellSize D (k+1) := by
  simp [down, mass, conductance, hp.ne', (shellSize_pos hD (k+1)).ne', mul_div_mul_left,
    mul_comm]

end Metropolis.Shell
