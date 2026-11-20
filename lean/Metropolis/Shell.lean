import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Metropolis.Shell

/-- Cardinality of an infinity-norm shell, as a real multiplicity. -/
def shellSize (D k : ℕ) : ℝ :=
  if k = 0 then 1 else (2 * (k : ℝ) + 1) ^ D - (2 * (k : ℝ) - 1) ^ D

/-- The finite expression for the shell-quotient escape time, with each
increment factored by its leading power of the inverse acceptance probability. -/
noncomputable def exactSum (D N : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, p⁻¹ ^ (k+1) / (2*(k:ℝ)+1)^(D-1) *
    (1 + ∑ m ∈ Finset.range k, shellSize D (m+1) * p^(m+1))

end Metropolis.Shell
