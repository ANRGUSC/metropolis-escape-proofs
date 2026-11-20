import Metropolis.Walk
import Mathlib.Logic.Relation

namespace Metropolis.Lattice
noncomputable section
variable {D : ℕ}

abbrev Path (x y : Site D) := Relation.ReflTransGen (fun u v => v ∈ neighbors u) x y

theorem step_add (x : Site D) (i : Fin D) (a b : ℤ) :
    step (step x i a) i b = step x i (a+b) := by
  funext j
  by_cases e : j = i
  · subst j; simp [step, add_assoc]
  · simp [step, Function.update_of_ne e]

theorem step_sign_mem (x : Site D) (i : Fin D) (b : Bool) :
    step x i (if b then 1 else -1) ∈ neighbors x :=
  Finset.mem_image.mpr ⟨(i,b), Finset.mem_univ _, rfl⟩

theorem coordinate_path (x : Site D) (i : Fin D) (t : ℤ) : Path x (step x i t) := by
  have hzero : step x i 0 = x := by funext j; by_cases h : j = i <;> simp [step,h]
  have pos (n : ℕ) : Path x (step x i (n : ℤ)) := by
    induction n with
    | zero => simpa [hzero] using (Relation.ReflTransGen.refl : Path x x)
    | succ n ih =>
      have e := step_sign_mem (step x i (n:ℤ)) i true
      simpa [step_add] using ih.tail e
  have neg (n : ℕ) : Path x (step x i (-(n : ℤ))) := by
    induction n with
    | zero => simpa [hzero] using (Relation.ReflTransGen.refl : Path x x)
    | succ n ih =>
      have e := step_sign_mem (step x i (-(n:ℤ))) i false
      simpa [step_add, neg_add, sub_eq_add_neg, add_comm] using ih.tail e
  cases t with
  | ofNat n => exact pos n
  | negSucc n => exact neg (n+1)

theorem lattice_path (x y : Site D) : Path x y := by
  classical
  let mixed (s : Finset (Fin D)) : Site D := fun j => if j ∈ s then y j else x j
  have h (s : Finset (Fin D)) : Path x (mixed s) := by
    induction s using Finset.induction_on with
    | empty => simpa [mixed] using (Relation.ReflTransGen.refl : Path x x)
    | @insert i s hi ih =>
      have e : step (mixed s) i (y i - mixed s i) = mixed (insert i s) := by
        funext j
        by_cases hj : j = i
        · subst j; simp [step, mixed]
        · simp [step, Function.update_of_ne hj, mixed, hj]
      rw [← e]; exact ih.trans (coordinate_path _ _ _)
  simpa [mixed] using h Finset.univ

theorem transition_pos_of_neighbor {p : ℝ} (hp : 0 < p) {x y : Site D} (hy : y ∈ neighbors x) :
    0 < transition p x y := by
  have ne : x ≠ y := by rintro rfl; exact not_neighbor_self x hy
  obtain ⟨⟨i,b⟩, _, _⟩ := Finset.mem_image.mp hy
  have hD : 0 < D := Nat.zero_lt_of_lt i.isLt
  simp only [transition, prob, if_neg ne, ENNReal.ofReal_pos, move, if_pos hy, edgeMass]
  exact div_pos (div_pos (pow_pos hp _) (by positivity)) (mass_pos p hp _)
end
end Metropolis.Lattice
