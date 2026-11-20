import Metropolis.Walk
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

namespace Metropolis.Lattice
open Finset
noncomputable section
variable {D : ℕ}

/-- Mean after one reflected/rejected Metropolis step, on the finite support
of the transition row. -/
def edgeRowMean (p : ℝ) (h : Site D → ℝ) (x : Site D) : ℝ :=
  ∑ y ∈ insert x (neighbors x), prob p x y * h y

private theorem direction_injective (x : Site D) :
    Function.Injective (fun d : Fin D × Bool => step x d.1 (if d.2 then 1 else -1)) := by
  rintro ⟨i,s⟩ ⟨j,t⟩ eq
  have h := congrFun eq i
  by_cases hij : i=j
  · subst j
    cases s <;> cases t <;> simp_all [step]
  · cases s <;> cases t <;> simp [step,Function.update_of_ne hij] at h

private theorem adjacent_mass_move {p : ℝ} (hp : 0 < p) {x y : Site D} (hne : y ∈ neighbors x) :
    mass p x * move p x y = edgeMass p x y := by
  simp only [move, if_pos hne]
  field_simp [(mass_pos p hp x).ne']

def currentDiff (p : ℝ) (h : Site D → ℝ) (x : Site D) (i : Fin D) : ℝ :=
  conductance p x i * (h x - h (step x i 1))

theorem residual_as_edges {p : ℝ} (hp : 0 < p) (h : Site D → ℝ) (x : Site D) :
    mass p x * (h x - edgeRowMean p h x) =
      ∑ i, (currentDiff p h x i - currentDiff p h (step x i (-1)) i) := by
  classical
  have weighted : mass p x * (h x - edgeRowMean p h x) =
      ∑ y ∈ neighbors x, edgeMass p x y * (h x-h y) := by
    unfold edgeRowMean
    rw [Finset.sum_insert (not_neighbor_self x)]
    simp only [prob, ite_true, eq_self]
    have hoff (y) (hy : y ∈ neighbors x) : x ≠ y := fun e => not_neighbor_self x (e ▸ hy)
    have hh : ∑ y ∈ neighbors x, (if x=y then 1-∑ z ∈ neighbors x, move p x z else move p x y)*h y =
        ∑ y ∈ neighbors x, move p x y*h y := Finset.sum_congr rfl fun y hy => by rw [if_neg (hoff y hy)]
    rw [hh]
    have he (y) (hy : y ∈ neighbors x) : edgeMass p x y = mass p x * move p x y :=
      (adjacent_mass_move hp hy).symm
    rw [show (∑ y ∈ neighbors x, edgeMass p x y * (h x - h y)) =
        ∑ y ∈ neighbors x, mass p x*(move p x y*h x - move p x y*h y) from
          Finset.sum_congr rfl fun y hy => by rw [he y hy]; ring]
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  rw [weighted]
  unfold neighbors
  rw [Finset.sum_image (fun _ _ _ _ e => direction_injective x e)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  have cancel : step (step x i (-1)) i 1 = x := step_cancel x i (-1)
  simp [currentDiff, edgeMass, conductance, cancel, max_comm (level x)]
  ring

end
end Metropolis.Lattice
