import Metropolis.ShellContract

namespace Metropolis.Shell

theorem exactSum_eq_paper (D N : ℕ) {p : ℝ} (hp : 0 < p) :
    exactSum D N p = paperSum D N p := by
  unfold exactSum paperSum
  apply Finset.sum_congr rfl
  intro k hk
  have hcancel (m : ℕ) (hm : m ∈ Finset.range k) :
      p⁻¹^(k+1) * p^(m+1) = p⁻¹^(k-m) := by
    have h : k+1 = (k-m)+(m+1) := by simp only [Finset.mem_range] at hm; omega
    rw [h, pow_add, mul_assoc, show p⁻¹^(m+1) = (p^(m+1))⁻¹ by rw [inv_pow],
      inv_mul_cancel₀ (pow_ne_zero _ hp.ne'), mul_one]
  have hs : p⁻¹^(k+1) * (∑ m ∈ Finset.range k, shellSize D (m+1) * p^(m+1)) =
      ∑ m ∈ Finset.range k, shellSize D (m+1) * p⁻¹^(k-m) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [mul_left_comm, hcancel m hm]
  rw [div_mul_eq_mul_div, mul_add, mul_one, hs]

theorem paper_exact_escape : ExactEscapeStatement := by
  intro D N hD p hp hp1
  refine ⟨meanTime_summable hD N hp hp1, (exact_escape hD N hp hp1).trans
    (exactSum_eq_paper D N hp), ?_⟩
  rintro rfl
  exact (line_exact_escape N hp hp1).trans (exactSum_eq_paper 1 N hp)

#print axioms paper_exact_escape
end Metropolis.Shell
