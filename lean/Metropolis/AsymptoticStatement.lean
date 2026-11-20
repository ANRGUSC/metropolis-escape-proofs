import Metropolis.ShellAbsorption
import Mathlib.Analysis.Asymptotics.Defs

open Filter
open scoped Asymptotics

namespace Metropolis.Asymptotic

/-- Theorem 2: the mean shell escape time, defined by survival probabilities,
has the stated two-sided asymptotic rate for every positive dimension. -/
def ShellScalingStatement : Prop :=
  ∀ (D : ℕ), 1 ≤ D → ∀ (p : ℝ), 0 < p → p < 1 →
    (fun N : ℕ => Shell.meanTime D N p 0) =Θ[atTop]
      (fun N : ℕ => (1 / p)^N / (N : ℝ)^(D - 1))

end Metropolis.Asymptotic
