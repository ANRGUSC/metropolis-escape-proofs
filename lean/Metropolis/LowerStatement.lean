import Metropolis.Walk

open scoped ENNReal

namespace Metropolis.Lower
open Metropolis.Lattice

/-- Theorem 3, with the mean time defined via the pre-absorption occupation
kernel of the original Metropolis lattice walk. -/
def EscapeLowerStatement : Prop :=
  ∀ (D : ℕ), 1 ≤ D → ∀ (p : ℝ), 0 < p → p < 1 →
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 1 ≤ N →
      ENNReal.ofReal (c * ((1/p)^N / (N:ℝ)^(D-1))) ≤
        meanHitting p (0 : Site D) {x | level x = N}

end Metropolis.Lower
