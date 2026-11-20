import Metropolis.Lattice
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open scoped ENNReal
namespace Metropolis.Lattice
noncomputable section
variable {D : ℕ}

/-- Sum over the positive coordinate orientation; each unoriented edge occurs once. -/
def dirichlet (p : ℝ) (f : Site D → ℝ) : ℝ≥0∞ :=
  ∑' xi : Site D × Fin D, ENNReal.ofReal (conductance p xi.1 xi.2 *
    (f xi.1 - f (step xi.1 xi.2 1))^2)

def capacity (p : ℝ) (a : Site D) (A : Set (Site D)) : ℝ≥0∞ :=
  ⨅ (f : Site D → ℝ) (_ : f a = 1) (_ : ∀ x ∈ A, f x = 0), dirichlet p f

theorem capacity_le_test (p : ℝ) (a : Site D) (A : Set (Site D)) (f : Site D → ℝ)
    (ha : f a = 1) (hA : ∀ x ∈ A, f x = 0) : capacity p a A ≤ dirichlet p f :=
  iInf_le_of_le f (iInf_le_of_le ha (iInf_le_of_le hA le_rfl))
end
end Metropolis.Lattice
