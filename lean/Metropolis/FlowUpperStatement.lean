import Metropolis.FlowResistance

namespace Metropolis.Flow
/-- Proposition 2, expressed using the infimum of unit-current energies on
the positive-coordinate edges of the full lattice. The constant is uniform
in the basin depth for fixed dimension and acceptance probability. -/
def UpperStatement : Prop :=
  ∀ (D : ℕ), 1 ≤ D → ∀ p : ℝ, 0 < p → p < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      resistance p (face (D-1) N) ≤ C * (p⁻¹^N / (N:ℝ)^(D-1))
end Metropolis.Flow
