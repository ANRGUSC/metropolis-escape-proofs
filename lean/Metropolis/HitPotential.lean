import Metropolis.Walk
import Metropolis.Potential

open scoped ENNReal
open Finset
noncomputable section
namespace Metropolis.Lattice
variable {D : ℕ}

def stopped (p : ℝ) (A : Set (Site D)) : Green.Kernel (Site D) := by
  classical exact Green.killed (transition p) A
def hit (p : ℝ) (a : Site D) (A : Set (Site D)) (x : Site D) : ℝ :=
  (Green.entrance (stopped p A) a x).toReal
def rowMean (p : ℝ) (f : Site D → ℝ) (x : Site D) : ℝ :=
  ∑ y ∈ insert x (neighbors x), prob p x y * f y

theorem prob_nonneg {p : ℝ} (hD : 0 < D) (hp : 0 < p) (hp1 : p ≤ 1) (x y : Site D) :
    0 ≤ prob p x y := by
  unfold prob
  split_ifs
  · exact sub_nonneg.mpr (outgoing_le_one hD hp hp1 _)
  · exact (move_bounds hD hp hp1 _ _).1

theorem stopped_substochastic {p : ℝ} (hD : 0 < D) (hp : 0 < p) (hp1 : p ≤ 1)
    (A : Set (Site D)) (x : Site D) : ∑' y, stopped p A x y ≤ 1 := by
  classical
  rw [← transition_stochastic hD hp hp1 x]
  apply ENNReal.tsum_le_tsum; intro y; simp [stopped, Green.killed]; split_ifs <;> simp

theorem entrance_finite {p : ℝ} (hD : 0 < D) (hp : 0 < p) (hp1 : p ≤ 1)
    (A : Set (Site D)) (a x : Site D) : Green.entrance (stopped p A) a x ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (Green.entrance_le_one (stopped_substochastic hD hp hp1 A) a x)

theorem hit_bounds {p : ℝ} (hD : 0 < D) (hp : 0 < p) (hp1 : p ≤ 1)
    (A : Set (Site D)) (a x : Site D) : 0 ≤ hit p a A x ∧ hit p a A x ≤ 1 := by
  refine ⟨ENNReal.toReal_nonneg, ?_⟩
  simpa [hit] using ENNReal.toReal_mono ENNReal.one_ne_top
    (Green.entrance_le_one (stopped_substochastic hD hp hp1 A) a x)

theorem hit_at (p : ℝ) (A : Set (Site D)) (a : Site D) : hit p a A a = 1 := by
  simp [hit, Green.entrance_at]

theorem entrance_target (p : ℝ) {A : Set (Site D)} {a x : Site D} (ha : a ∉ A) (hx : x ∈ A) :
    Green.entrance (stopped p A) a x = 0 := by
  classical
  have ne : x ≠ a := by rintro rfl; exact ha hx
  rw [Green.entrance_away _ _ _ ne]
  simp [stopped, Green.killed, hx]

theorem hit_target (p : ℝ) {A : Set (Site D)} {a x : Site D} (ha : a ∉ A) (hx : x ∈ A) :
    hit p a A x = 0 := by simp [hit, entrance_target p ha hx]

theorem prob_off {p : ℝ} {x y : Site D} (h : y ∉ insert x (neighbors x)) :
    prob p x y = 0 := by
  simp only [mem_insert, not_or] at h
  simp [prob, Ne.symm h.1, move, h.2]

theorem rowMean_ofReal {p : ℝ} (hD : 0 < D) (hp : 0 < p) (hp1 : p ≤ 1)
    {f : Site D → ℝ} (hf : ∀ x, 0 ≤ f x) (x : Site D) :
    ENNReal.ofReal (rowMean p f x) = ∑' y, transition p x y * ENNReal.ofReal (f y) := by
  rw [tsum_eq_sum (s:=insert x (neighbors x))]
  · unfold rowMean
    rw [ENNReal.ofReal_sum_of_nonneg (fun y _ => mul_nonneg (prob_nonneg hD hp hp1 x y) (hf y))]
    simp only [transition, ENNReal.ofReal_mul (prob_nonneg hD hp hp1 x _)]
  · intro y hy; simp [transition, prob_off hy]

theorem stopped_row_entrance {p : ℝ} (hD : 0 < D) (hp : 0 < p) (hp1 : p ≤ 1)
    {A : Set (Site D)} {a x : Site D} (ha : a ∉ A) (hx : x ∉ A) :
    (∑' z, stopped p A x z * Green.entrance (stopped p A) a z) =
      ENNReal.ofReal (rowMean p (hit p a A) x) := by
  classical
  rw [rowMean_ofReal hD hp hp1 (fun y => (hit_bounds hD hp hp1 A a y).1)]
  apply tsum_congr; intro z
  simp only [hit, ENNReal.ofReal_toReal (entrance_finite hD hp hp1 _ _ _)]
  by_cases hz : z ∈ A
  · simp [entrance_target p ha hz]
  · simp [stopped, Green.killed, hx,hz]

theorem hit_harmonic {p : ℝ} (hD : 0 < D) (hp : 0 < p) (hp1 : p ≤ 1)
    {A : Set (Site D)} {a x : Site D} (ha : a ∉ A) (hx : x ∉ A) (hne : x ≠ a) :
    hit p a A x = rowMean p (hit p a A) x := by
  unfold hit
  rw [Green.entrance_away _ _ _ hne, stopped_row_entrance hD hp hp1 ha hx]
  apply ENNReal.toReal_ofReal
  exact Finset.sum_nonneg fun y _ => mul_nonneg (prob_nonneg hD hp hp1 x y) ENNReal.toReal_nonneg
end Metropolis.Lattice
end
