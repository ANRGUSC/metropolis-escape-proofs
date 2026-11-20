import Metropolis.ShellLine

namespace Metropolis.Shell

/-- The printed expression, separating the origin from positive source shells. -/
noncomputable def paperSum (D N : ℕ) (p : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N,
    (p⁻¹^(k+1) + ∑ m ∈ Finset.range k, shellSize D (m+1) * p⁻¹^(k-m)) /
      (2*(k:ℝ)+1)^(D-1)

/-- Both assertions in Theorem 1 including the unbiased uphill case. -/
def ExactEscapeStatement : Prop :=
  ∀ D N : ℕ, 0 < D → ∀ p : ℝ, 0 < p → p ≤ 1 →
    (∀ k, Summable (fun n => survival N (fun j => up D j p) (fun j => down D j p) n k)) ∧
    meanTime D N p 0 = paperSum D N p ∧
    (D = 1 → (∑' n, lineSurvival N p n 0) = paperSum D N p)

end Metropolis.Shell
