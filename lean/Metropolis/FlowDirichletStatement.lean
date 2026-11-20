import Metropolis.FlowResistance
import Metropolis.Capacity

namespace Metropolis.Flow
/-- The manuscript's point-to-face effective resistance is the reciprocal
of Dirichlet capacity on the whole Metropolis lattice. -/
def FaceResistanceStatement : Prop :=
  ∀ (D : ℕ), 1 ≤ D → ∀ (p : ℝ), 0 < p → p < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      (Lattice.capacity p 0 (face (D-1) N))⁻¹ ≤ ENNReal.ofReal (C * ((1/p)^N / (N:ℝ)^(D-1)))
end Metropolis.Flow
