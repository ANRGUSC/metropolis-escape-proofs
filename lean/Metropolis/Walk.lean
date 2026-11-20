import Metropolis.Capacity
import Metropolis.Green
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

open scoped ENNReal
open Finset
namespace Metropolis.Lattice
noncomputable section
variable {D : ℕ}

/-- The sites accessible by a single unit coordinate proposal. -/
def neighbors (x : Site D) : Finset (Site D) :=
  univ.image fun d : Fin D × Bool => step x d.1 (if d.2 then 1 else -1)

theorem neighbor_symm (x y : Site D) : y ∈ neighbors x ↔ x ∈ neighbors y := by
  have flip (u v : Site D) (h : v ∈ neighbors u) : u ∈ neighbors v := by
    obtain ⟨⟨i,b⟩, _, rfl⟩ := Finset.mem_image.mp h
    apply Finset.mem_image.mpr
    refine ⟨(i,!b), Finset.mem_univ _, ?_⟩
    cases b
    · simpa using step_cancel u i (-1)
    · simpa using step_cancel u i 1
  exact ⟨flip x y, flip y x⟩

theorem not_neighbor_self (x : Site D) : x ∉ neighbors x := by
  intro h
  obtain ⟨⟨i,b⟩, _, e⟩ := Finset.mem_image.mp h
  have a := congrFun e i
  cases b <;> simp [step] at a

def edgeMass (p : ℝ) (x y : Site D) : ℝ :=
  p ^ max (level x) (level y) / (2 * (D:ℝ))

def move (p : ℝ) (x y : Site D) : ℝ :=
  if y ∈ neighbors x then edgeMass p x y / mass p x else 0

/-- The diagonal contains all rejected proposals. An accepted nearest-neighbor
move has probability min(μ(x), μ(y))/(2D μ(x)). -/
def prob (p : ℝ) (x y : Site D) : ℝ :=
  if x = y then 1 - ∑ z ∈ neighbors x, move p x z else move p x y

def transition (p : ℝ) (x y : Site D) : ℝ≥0∞ := ENNReal.ofReal (prob p x y)

theorem transition_balance {p : ℝ} (hp : 0 < p) :
    Green.Balance (fun x : Site D => ENNReal.ofReal (mass p x)) (transition p) := by
  intro x y
  by_cases h : x = y
  · subst y; rfl
  · have mx := mass_pos p hp x
    have my := mass_pos p hp y
    simp only [transition, prob, if_neg h, if_neg (Ne.symm h), ← ENNReal.ofReal_mul mx.le,
      ← ENNReal.ofReal_mul my.le]
    by_cases hn : y ∈ neighbors x
    · simp only [move, if_pos hn, if_pos ((neighbor_symm x y).mp hn)]
      congr 1
      rw [mul_comm (mass p x), div_mul_cancel₀ _ mx.ne', mul_comm (mass p y), div_mul_cancel₀ _ my.ne']
      simp [edgeMass, max_comm]
    · simp [move, hn, mt (neighbor_symm x y).mpr hn]

theorem move_bounds {p : ℝ} (hD : 0 < D) (hp : 0 < p) (hp1 : p ≤ 1) (x y : Site D) :
    0 ≤ move p x y ∧ move p x y ≤ 1 / (2 * (D:ℝ)) := by
  have hd : 0 < (2 * (D:ℝ)) := mul_pos (by norm_num) (by exact_mod_cast hD)
  have hx := mass_pos p hp x
  have he : p ^ max (level x) (level y) ≤ mass p x :=
    pow_le_pow_of_le_one hp.le hp1 (le_max_left _ _)
  unfold move edgeMass
  split_ifs
  · constructor
    · positivity
    · rw [div_le_div_iff₀ hx hd]
      calc
        _ = p ^ max (level x) (level y) := div_mul_cancel₀ _ hd.ne'
        _ ≤ _ := by simpa using he
  · exact ⟨le_rfl, by positivity⟩

theorem outgoing_le_one {p : ℝ} (hD : 0 < D) (hp : 0 < p) (hp1 : p ≤ 1) (x : Site D) :
    ∑ y ∈ neighbors x, move p x y ≤ 1 := by
  have card : (neighbors x).card ≤ 2*D := by
    simpa [neighbors, Nat.mul_comm] using (Finset.card_image_le (s:=univ)
      (f:=fun d : Fin D × Bool => step x d.1 (if d.2 then 1 else -1)))
  calc
    _ ≤ ∑ _y ∈ neighbors x, (1:ℝ)/(2*D) := Finset.sum_le_sum fun y _ => (move_bounds hD hp hp1 x y).2
    _ = ((neighbors x).card:ℝ)/(2*D) := by simp [div_eq_mul_inv]
    _ ≤ 1 := by
      apply (div_le_one (by positivity : 0 < 2*(D:ℝ))).mpr
      exact_mod_cast card

theorem transition_stochastic {p : ℝ} (hD : 0 < D) (hp : 0 < p) (hp1 : p ≤ 1)
    (x : Site D) : ∑' y, transition p x y = 1 := by
  classical
  let B := insert x (neighbors x)
  rw [tsum_eq_sum (s:=B)]
  · rw [Finset.sum_insert (not_neighbor_self x)]
    have h (y) (hy : y ∈ neighbors x) : transition p x y = ENNReal.ofReal (move p x y) := by
      have ne : x ≠ y := fun e => not_neighbor_self x (e ▸ hy)
      simp [transition, prob, ne]
    rw [Finset.sum_congr rfl h, ← ENNReal.ofReal_sum_of_nonneg (fun y _ => (move_bounds hD hp hp1 x y).1)]
    simp only [transition, prob, ite_true]
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr (outgoing_le_one hD hp hp1 x))
      (Finset.sum_nonneg fun y _ => (move_bounds hD hp hp1 x y).1)]
    simp
  · intro y hy
    have hn : y ∉ neighbors x := fun h => hy (Finset.mem_insert_of_mem h)
    have ne : x ≠ y := by rintro rfl; exact hy (Finset.mem_insert_self _ _)
    simp [transition, prob, ne, move, hn]

/-- Tail sum before first entry into the target, starting with time zero. -/
def meanHitting (p : ℝ) (a : Site D) (A : Set (Site D)) : ℝ≥0∞ := by
  classical
  exact if a ∈ A then 0 else Green.meanLifetime (Green.killed (transition p) A) a

end
end Metropolis.Lattice
