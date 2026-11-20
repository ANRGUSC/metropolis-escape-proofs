import Metropolis.Green
import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-! First entrance to a single state, including entrance at time zero. -/
open scoped ENNReal
open Finset
noncomputable section
namespace Metropolis.Green
variable {S : Type*} [DecidableEq S]

def first (P : Kernel S) (a : S) : ℕ → S → ℝ≥0∞
  | 0, x => identity x a
  | n+1, x => if x = a then 0 else ∑' z, P x z * first P a n z

def entrance (P : Kernel S) (a x : S) := ∑' n, first P a n x

theorem sum_interchange {α β : Type*} (s : Finset β) (f : α → β → ℝ≥0∞) :
    (∑' x, ∑ i ∈ s, f x i) = ∑ i ∈ s, ∑' x, f x i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, ENNReal.tsum_add, ih]

/-- Decompose a visit at time n by the exact time of first entrance to a. -/
theorem visit_decomposition (P : Kernel S) (a : S) (n : ℕ) (x : S) :
    steps P n x a = ∑ k ∈ range (n+1), first P a k x * steps P (n-k) a a := by
  induction n generalizing x with
  | zero => simp [steps, first, identity]
  | succ n ih =>
    rw [sum_range_succ']
    by_cases e : x = a
    · subst x
      simp [first, identity]
    · simp only [first, if_neg e, identity, zero_mul, add_zero]
      change (∑' z, P x z * steps P n z a) = _
      simp_rw [ih, Finset.mul_sum]
      rw [sum_interchange]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [Nat.add_sub_add_right, ← ENNReal.tsum_mul_right, mul_assoc]

/-- The first-hit decomposition summed over all times. -/
theorem occupation_first (P : Kernel S) (a x : S) :
    occupation P x a = entrance P a x * occupation P a a := by
  let F : ℕ × ℕ → ℝ≥0∞ := fun q => first P a q.1 x * steps P q.2 a a
  calc
    _ = ∑' n, ∑ q ∈ antidiagonal n, F q := by
      apply tsum_congr
      intro n
      rw [visit_decomposition P a n x, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    _ = ∑' q : Σ n : ℕ, ↥(antidiagonal n), F q.2 := by
      rw [ENNReal.tsum_sigma']
      apply tsum_congr
      intro n
      rw [tsum_fintype, Finset.sum_coe_sort]
    _ = ∑' q : ℕ × ℕ, F q := Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq F
    _ = _ := by
      rw [ENNReal.tsum_prod']
      simp only [F, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, entrance, occupation]

theorem entrance_le_one {P : Kernel S} (hrow : ∀ x, ∑' z, P x z ≤ 1) (a x : S) :
    entrance P a x ≤ 1 := by
  have bound (n : ℕ) (y : S) : ∑ t ∈ range (n+1), first P a t y ≤ 1 := by
    induction n generalizing y with
    | zero => by_cases e : y = a <;> simp [first, identity, e]
    | succ n ih =>
      rw [sum_range_succ']
      by_cases e : y = a
      · subst y; simp [first, identity]
      · simp only [first, if_neg e, identity, add_zero]
        rw [← sum_interchange]
        calc
          _ = ∑' z, P y z * ∑ t ∈ range (n+1), first P a t z := by simp [Finset.mul_sum]
          _ ≤ ∑' z, P y z := ENNReal.tsum_le_tsum fun z => by
            calc
              _ ≤ P y z * 1 := by gcongr; exact ih z
              _ = _ := mul_one _
          _ ≤ _ := hrow y
  unfold entrance
  rw [ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun n => le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono (Nat.le_succ n)) (by intros; positivity)) (bound n x)

end Metropolis.Green
end
