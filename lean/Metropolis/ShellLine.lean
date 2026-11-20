import Metropolis.ShellExpectation

namespace Metropolis.Shell

/-- The signed walk on the integer line chooses a direction uniformly. At a
nonzero site the outward proposal is accepted with probability p; the inward
proposal is always accepted. A zero contribution after reaching ±N kills the row. -/
noncomputable def lineKilled (N : ℕ) (p : ℝ) (f : ℤ → ℝ) (x : ℤ) : ℝ :=
  if x.natAbs < N then
    match x with
    | .ofNat 0 => p/2 * f 1 + p/2 * f (-1) + (1-p)*f 0
    | .ofNat (k+1) =>
      p/2 * f (.ofNat (k+2)) + (1/2) * f (.ofNat k) + (1-p)/2 * f (.ofNat (k+1))
    | .negSucc k =>
      p/2 * f (.negSucc (k+1)) + (1/2) * f (- (k:ℤ)) + (1-p)/2 * f (.negSucc k)
  else 0

noncomputable def lineSurvival (N : ℕ) (p : ℝ) : ℕ → ℤ → ℝ
  | 0, x => if x.natAbs < N then 1 else 0
  | n+1, x => lineKilled N p (lineSurvival N p n) x

private theorem line_intertwines (N : ℕ) {p : ℝ} (hp : 0 < p) (f : ℕ → ℝ) (x : ℤ) :
    lineKilled N p (fun x => f x.natAbs) x =
    killed N (fun j => up 1 j p) (fun j => down 1 j p) f x.natAbs := by
  have hs (k : ℕ) : shellSize 1 (k+1) = 2 := by
    simp only [shellSize, Nat.succ_ne_zero, if_false, pow_one]
    ring
  have hu (k : ℕ) : up 1 (k+1) p = p / 2 := by
    rw [up_eq (by decide) _ hp, hs]; simp [area]
  have hd (k : ℕ) : down 1 (k+1) p = 1 / 2 := by
    rw [down_succ (by decide) _ hp, hs]; simp [area]
  have absPos (j : ℕ) : (Int.ofNat j).natAbs = j := rfl
  cases x with
  | ofNat j =>
    cases j with
    | zero =>
      simp only [lineKilled, killed, absPos, up_zero, down, if_true]
      split <;> simp <;> ring
    | succ k =>
      simp only [lineKilled, killed, absPos, Nat.succ_eq_add_one, hu, hd, Nat.add_sub_cancel]
      split <;> ring
  | negSucc k =>
    simp only [lineKilled, killed, Int.natAbs_negSucc, Int.natAbs_neg, Int.natAbs_natCast,
      Nat.succ_eq_add_one, hu, hd, Nat.add_sub_cancel]
    split <;> ring

theorem line_survival_eq (N : ℕ) {p : ℝ} (hp : 0 < p) (n : ℕ) (x : ℤ) :
    lineSurvival N p n x = survival N (fun j => up 1 j p) (fun j => down 1 j p) n x.natAbs := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    change lineKilled N p (lineSurvival N p n) x = _
    rw [show lineSurvival N p n = _ from funext ih]
    exact line_intertwines N hp _ x

theorem line_exact_escape (N : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    ∑' n, lineSurvival N p n 0 = exactSum 1 N p := by
  simp_rw [line_survival_eq N hp]
  exact exact_escape (by decide) N hp hp1

end Metropolis.Shell
