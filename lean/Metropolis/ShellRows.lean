import Metropolis.ShellPoisson

namespace Metropolis.Shell

/-- The shell occupancy covers the two faces appearing in the neighboring
transition numerators. This also handles the smallest nonzero shell. -/
theorem shellSize_faces {D : ℕ} (hD : 0 < D) (k : ℕ) :
    area D (k+1) + area D k ≤ shellSize D (k+1) := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD)
  let a : ℝ := 2*(k:ℝ)+1
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hab : a ≤ a+2 := by linarith
  have hp : a^d ≤ (a+2)^d := pow_le_pow_left₀ ha hab d
  have hm := mul_le_mul_of_nonneg_left hp ha
  simp only [area, shellSize, Nat.succ_ne_zero, if_false, Nat.cast_add, Nat.cast_one,
    Nat.succ_sub_one]
  have e₁ : 2*((k:ℝ)+1)+1 = a+2 := by dsimp [a]; ring
  have e₂ : 2*((k:ℝ)+1)-1 = a := by dsimp [a]; ring
  rw [e₁,e₂]
  change (a+2)^d + a^d ≤ (a+2)^(d+1) - a^(d+1)
  rw [pow_succ, pow_succ]
  nlinarith

theorem row_probabilities {D : ℕ} (hD : 0 < D) {p : ℝ} (hp : 0 < p)
    (hp1 : p ≤ 1) (k : ℕ) :
    0 ≤ up D k p ∧ 0 ≤ down D k p ∧ up D k p + down D k p ≤ 1 := by
  cases k with
  | zero => simpa [up_zero, down, hp.le] using hp1
  | succ k =>
    rw [up_eq hD _ hp, down_succ hD k hp]
    have hs := shellSize_pos hD (k+1)
    have ha := area_pos D (k+1)
    refine ⟨div_nonneg (mul_nonneg hp.le ha.le) hs.le,
      div_nonneg (area_pos D k).le hs.le, ?_⟩
    rw [← add_div, div_le_one hs]
    have hu : p * area D (k+1) ≤ area D (k+1) := by
      simpa using mul_le_mul_of_nonneg_right hp1 ha.le
    exact (add_le_add hu le_rfl).trans (shellSize_faces hD k)

theorem increment_nonneg {D : ℕ} (hD : 0 < D) {p : ℝ} (hp : 0 < p) (k : ℕ) :
    0 ≤ increment D k p := by
  unfold increment prefixMass
  have hsum : 0 ≤ ∑ m ∈ Finset.range k, shellSize D (m+1) * p^(m+1) :=
    Finset.sum_nonneg fun m _ => (mass_pos hD (m+1) hp).le
  have ha := area_pos D k
  positivity

theorem exactSum_succ (D n : ℕ) (p : ℝ) :
    exactSum D (n+1) p = exactSum D n p + increment D n p := by
  simp [exactSum, increment, prefixMass, area, Finset.sum_range_succ]

theorem exactSum_mono {D : ℕ} (hD : 0 < D) {p : ℝ} (hp : 0 < p) :
    Monotone (fun n => exactSum D n p) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [exactSum_succ]
  linarith [increment_nonneg hD hp n]

/-- Solution candidate at every shell, with extension by zero beyond the target. -/
noncomputable def potential (D N : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  exactSum D N p - exactSum D (min k N) p

theorem potential_drop (D N : ℕ) (p : ℝ) {k : ℕ} (hk : k < N) :
    potential D N p k - potential D N p (k+1) = increment D k p := by
  simp only [potential, min_eq_left hk.le, min_eq_left (Nat.succ_le_of_lt hk),
    exactSum_succ]
  ring

end Metropolis.Shell
