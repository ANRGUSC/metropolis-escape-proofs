import Metropolis.ShellCrossings
import Metropolis.ShellQuotientContract

namespace Metropolis.Shell

/-- Proposition 1. The numerator sums all original inside-to-outside adjacent
pairs in B_N, and the denominator sums the original masses of the shell sites. -/
def FullQuotientStatement : Prop :=
  ∀ d N : ℕ, ∀ p : ℝ, 0 < p → p ≤ 1 →
    (∀ x y : Cube (d+1) N,
      p^(height x) * latticeRow p x y = p^(height y) * latticeRow p y x) ∧
    (∀ k (hk : k < N), Function.Bijective (@crossMap d N k hk)) ∧
    (∀ k (hk : k+1 < N),
      actualLink d N (k+1) p / shortedMass d N (k+1) hk.le p =
        p * area (d+1) (k+1) / shellSize (d+1) (k+1) ∧
      actualLink d N k p / shortedMass d N (k+1) hk.le p =
        area (d+1) k / shellSize (d+1) (k+1)) ∧
    (∀ hn : 0 < N, actualLink d N 0 p / shortedMass d N 0 hn.le p = p)

end Metropolis.Shell
