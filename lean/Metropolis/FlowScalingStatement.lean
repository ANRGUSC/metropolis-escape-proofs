import Metropolis.Walk
import Mathlib.Analysis.Asymptotics.Defs

open Filter
open scoped ENNReal Asymptotics
namespace Metropolis.Flow
open Metropolis.Lattice

/-- True-chain lifetime is finite at every positive depth. Its real value has
the advertised two-sided asymptotic order as the depth tends to infinity. -/
def TrueScalingStatement : Prop :=
  ∀ (D : ℕ), 1 ≤ D → ∀ (p : ℝ), 0 < p → p < 1 →
    (∀ N : ℕ, 1 ≤ N → meanHitting p (0 : Site D) {x | level x = N} ≠ ∞) ∧
    (fun N : ℕ => (meanHitting p (0 : Site D) {x | level x = N}).toReal) =Θ[atTop]
      (fun N : ℕ => (1/p)^N / (N:ℝ)^(D-1))

end Metropolis.Flow
