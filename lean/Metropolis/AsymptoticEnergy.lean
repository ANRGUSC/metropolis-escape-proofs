import Metropolis.AsymptoticKernel

open Finset

namespace Metropolis.Asymptotic

/-- Polynomial-geometric endpoint estimate used after adding the disjoint
forward and lateral flow energies in Proposition 2. -/
theorem energy_sum_bound (r : ℕ) {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 0 < N →
      (∑ k ∈ range N, p⁻¹^(k+1) / ((k:ℝ)+1)^r) ≤
        K * (p⁻¹^N / (N:ℝ)^r) := by
  have hw : 1 ≤ ∑' j, weight r p j := by
    simpa [weight] using weight_partial_le r hp hp' 1
  refine ⟨2^r * ∑' j, weight r p j, mul_pos (by positivity) (by linarith), ?_⟩
  intro N hN
  have hu := (sum_steps_bounds r hp hp' (fun _ => 1) 1 (fun _ => ⟨le_rfl, le_rfl⟩) N hN).2
  simp only [mul_one, one_mul] at hu
  calc _ ≤ ∑ k ∈ range N, 2^r * (p⁻¹^(k+1) / (2*(k:ℝ)+1)^r) := by
          apply sum_le_sum
          intro k _
          rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
          have h : (2*(k:ℝ)+1)^r ≤ 2^r * ((k:ℝ)+1)^r := by
            rw [← mul_pow]
            apply pow_le_pow_left₀ (by positivity)
            linarith
          calc _ ≤ p⁻¹^(k+1) * (2^r * ((k:ℝ)+1)^r) :=
                    mul_le_mul_of_nonneg_left h (by positivity)
               _ = _ := by ring
       _ = 2^r * (∑ k ∈ range N, p⁻¹^(k+1) / (2*(k:ℝ)+1)^r) := (mul_sum ..).symm
       _ ≤ 2^r * ((∑' j, weight r p j) * (p⁻¹^N / (N:ℝ)^r)) :=
             mul_le_mul_of_nonneg_left hu (by positivity)
       _ = _ := by ring

end Metropolis.Asymptotic
