import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! The killed occupation kernel on a countable state space, in units of visits.
Its row sum counts the expected number of pre-absorption time steps. -/
namespace Metropolis.Green
open scoped ENNReal
noncomputable section
variable {S : Type*} [DecidableEq S]

abbrev Kernel (S : Type*) := S → S → ℝ≥0∞

def identity : Kernel S := fun x y => if x = y then 1 else 0
def compose (P Q : Kernel S) : Kernel S := fun x y => ∑' z, P x z * Q z y

theorem compose_assoc (P Q R : Kernel S) :
    compose (compose P Q) R = compose P (compose Q R) := by
  funext x y
  simp only [compose, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

theorem compose_identity (P : Kernel S) : compose P identity = P := by
  funext x y
  simp [compose, identity, mul_ite]

theorem identity_compose (P : Kernel S) : compose identity P = P := by
  funext x y
  simp [compose, identity, ite_mul]

def steps (P : Kernel S) : ℕ → Kernel S
  | 0 => identity
  | n+1 => compose P (steps P n)

theorem steps_right (P : Kernel S) (n : ℕ) :
    steps P (n+1) = compose (steps P n) P := by
  induction n with
  | zero => simp [steps, compose_identity, identity_compose]
  | succ n ih => change compose P (steps P (n+1)) = compose (compose P (steps P n)) P
                 rw [ih, compose_assoc]

def Balance (μ : S → ℝ≥0∞) (P : Kernel S) : Prop :=
  ∀ x y, μ x * P x y = μ y * P y x

def killed (P : Kernel S) (A : Set S) [DecidablePred (· ∈ A)] : Kernel S :=
  fun x y => if x ∈ A ∨ y ∈ A then 0 else P x y

theorem killed_balance {P : Kernel S} {μ : S → ℝ≥0∞} (h : Balance μ P)
    (A : Set S) [DecidablePred (· ∈ A)] : Balance μ (killed P A) := by
  intro x y
  by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp [killed, hx, hy, h x y]

theorem steps_balance {P : Kernel S} {μ : S → ℝ≥0∞} (h : Balance μ P)
    (n : ℕ) : Balance μ (steps P n) := by
  induction n with
  | zero =>
    intro x y
    by_cases e : x = y
    · subst y; rfl
    · simp [steps, identity, e, Ne.symm e]
  | succ n ih =>
    intro x y
    calc
      μ x * steps P (n+1) x y = ∑' z, (μ x * P x z) * steps P n z y := by
        simp only [steps, compose, mul_assoc, ENNReal.tsum_mul_left]
      _ = ∑' z, (μ y * steps P n y z) * P z x := by
        apply tsum_congr
        intro z
        rw [h x z, ← ih z y]
        ac_rfl
      _ = μ y * steps P (n+1) y x := by
        rw [steps_right P n]
        simp only [compose, mul_assoc, ENNReal.tsum_mul_left]

def occupation (P : Kernel S) (x y : S) : ℝ≥0∞ := ∑' n, steps P n x y

theorem occupation_balance {P : Kernel S} {μ : S → ℝ≥0∞} (h : Balance μ P) :
    Balance μ (occupation P) := by
  intro x y
  simp only [occupation, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun n => steps_balance h n x y

/-- Starting outside the target, this sums the survival probability at each time. -/
def meanLifetime (P : Kernel S) (x : S) : ℝ≥0∞ := ∑' n, ∑' y, steps P n x y

theorem meanLifetime_eq_total_occupation (P : Kernel S) (x : S) :
    meanLifetime P x = ∑' y, occupation P x y := ENNReal.tsum_comm

#print axioms occupation_balance
end
end Metropolis.Green
