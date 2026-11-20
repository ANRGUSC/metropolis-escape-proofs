import Metropolis.ShellPoisson
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace Metropolis.Shell

/-- The killed row of the walk. A visit to the target contributes zero
subsequent survival probability. Only the states below the target are transient. -/
noncomputable def killed (N : ℕ) (u v : ℕ → ℝ) (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  if k < N then u k * f (k+1) + v k * f (k-1) + (1-u k-v k) * f k else 0

/-- Probability of surviving more than n steps, obtained by multiplying the
killed transition matrix n times by the indicator of the transient states. -/
noncomputable def survival (N : ℕ) (u v : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, k => if k < N then 1 else 0
  | n+1, k => killed N u v (survival N u v n) k

/-- Tail-sum definition of the expectation of an integer-valued hitting time. -/
noncomputable def meanTime (D N : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  ∑' n, survival N (fun j => up D j p) (fun j => down D j p) n k

theorem kill_mono {N : ℕ} {u v : ℕ → ℝ}
    (prob : ∀ k < N, 0 ≤ u k ∧ 0 ≤ v k ∧ u k + v k ≤ 1)
    {f g : ℕ → ℝ} (fg : ∀ k, f k ≤ g k) (k : ℕ) :
    killed N u v f k ≤ killed N u v g k := by
  unfold killed
  split_ifs with h
  · obtain ⟨hu,hv,huv⟩ := prob k h
    exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left (fg _) hu)
      (mul_le_mul_of_nonneg_left (fg _) hv))
      (mul_le_mul_of_nonneg_left (fg _) (by linarith))
  · rfl

theorem survival_nonneg {N : ℕ} {u v : ℕ → ℝ}
    (prob : ∀ k < N, 0 ≤ u k ∧ 0 ≤ v k ∧ u k + v k ≤ 1) (n k : ℕ) :
    0 ≤ survival N u v n k := by
  induction n generalizing k with
  | zero => simp only [survival]; split <;> norm_num
  | succ n ih =>
    have h := kill_mono prob (f := fun _ => 0) (g := survival N u v n) ih k
    simpa [survival, killed] using h

theorem sum_survival_succ (N : ℕ) (u v : ℕ → ℝ) (n k : ℕ) :
    ∑ i ∈ Finset.range (n+1), survival N u v i k =
      (if k < N then 1 else 0) +
      killed N u v (fun j => ∑ i ∈ Finset.range n, survival N u v i j) k := by
  rw [Finset.sum_range_succ']
  simp only [survival, killed]
  split_ifs <;> simp [Finset.sum_add_distrib, Finset.mul_sum, add_comm]

/-- A nonnegative solution of the mean first-step equations bounds all the
finite-horizon expectations. Taking the tail sum therefore gives a finite
expectation satisfying the same first-step equations. -/
theorem mean_equations {N : ℕ} {u v F : ℕ → ℝ}
    (prob : ∀ k < N, 0 ≤ u k ∧ 0 ≤ v k ∧ u k + v k ≤ 1)
    (pos : ∀ k, 0 ≤ F k)
    (equation : ∀ k, F k = (if k < N then 1 else 0) + killed N u v F k) :
    let T := fun k => ∑' n, survival N u v n k
    (∀ k, Summable (fun n => survival N u v n k)) ∧
    ∀ k, T k = (if k < N then 1 else 0) + killed N u v T k := by
  dsimp only
  have bounded (n k : ℕ) : ∑ i ∈ Finset.range n, survival N u v i k ≤ F k := by
    induction n generalizing k with
    | zero => simpa using pos k
    | succ n ih =>
      rw [sum_survival_succ, equation k]
      exact add_le_add le_rfl (kill_mono prob ih k)
  have hs (k : ℕ) : Summable (fun n => survival N u v n k) :=
    summable_of_sum_range_le (fun n => survival_nonneg prob n k) (fun n => bounded n k)
  refine ⟨hs, fun k => ?_⟩
  rw [← (hs k).sum_add_tsum_nat_add 1]
  simp only [Finset.sum_range_one, survival]
  by_cases hk : k < N
  · simp only [killed, if_pos hk]
    have hu := (hs (k+1)).mul_left (u k)
    have hv := (hs (k-1)).mul_left (v k)
    have hr := (hs k).mul_left (1-u k-v k)
    rw [(hu.add hv).tsum_add hr, hu.tsum_add hv]
    simp only [tsum_mul_left]
  · simp [killed, hk]

end Metropolis.Shell
