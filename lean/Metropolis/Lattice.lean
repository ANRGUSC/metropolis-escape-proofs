import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

namespace Metropolis.Lattice
noncomputable section
abbrev Site (D : ℕ) := Fin D → ℤ
variable {D : ℕ}

def step (x : Site D) (i : Fin D) (v : ℤ) : Site D := Function.update x i (x i + v)
def level (x : Site D) : ℕ := Finset.univ.sup fun i => (x i).natAbs
def mass (p : ℝ) (x : Site D) : ℝ := p ^ level x
def conductance (p : ℝ) (x : Site D) (i : Fin D) : ℝ :=
  p ^ max (level x) (level (step x i 1)) / (2 * (D : ℝ))

theorem step_cancel (x : Site D) (i : Fin D) (v : ℤ) :
    step (step x i v) i (-v) = x := by
  funext j
  by_cases h : j = i
  · subst j; simp [step]
  · simp [step, Function.update_of_ne h]

@[simp] theorem level_zero : level (0 : Site D) = 0 := by simp [level]
@[simp] theorem mass_zero (p : ℝ) : mass p (0 : Site D) = 1 := by simp [mass]
theorem mass_pos (p : ℝ) (hp : 0 < p) (x : Site D) : 0 < mass p x :=
  pow_pos hp _
theorem conductance_pos (p : ℝ) (hp : 0 < p) (x : Site D) (i : Fin D) :
    0 < conductance p x i := by
  have hd : 0 < D := Nat.zero_lt_of_lt i.isLt
  exact div_pos (pow_pos hp _) (mul_pos (by norm_num) (by exact_mod_cast hd))
end
end Metropolis.Lattice
