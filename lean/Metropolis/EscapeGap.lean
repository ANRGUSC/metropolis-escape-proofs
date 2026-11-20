import Metropolis.HitPotential
import Metropolis.Reachability

open scoped ENNReal
open Finset
noncomputable section
namespace Metropolis.Lattice
variable {D : ℕ}

theorem row_one {p : ℝ} (hD : 0 < D) (hp : 0 < p) (hp1 : p ≤ 1) (x : Site D) :
    ∑ y ∈ insert x (neighbors x), prob p x y = 1 := by
  have h := rowMean_ofReal hD hp hp1 (f:=fun _ : Site D => (1:ℝ)) (fun _ => zero_le_one) x
  simp only [rowMean, mul_one, ENNReal.ofReal_one, transition_stochastic hD hp hp1] at h
  have t := congrArg ENNReal.toReal h
  simpa [ENNReal.toReal_ofReal (Finset.sum_nonneg fun y _ => prob_nonneg hD hp hp1 x y)] using t

theorem rowMean_le_one {p : ℝ} (hD : 0 < D) (hp : 0 < p) (hp1 : p ≤ 1)
    {f : Site D → ℝ} (hf : ∀ x, f x ≤ 1) (x : Site D) : rowMean p f x ≤ 1 := by
  rw [← row_one hD hp hp1 x]
  apply Finset.sum_le_sum
  intro y _
  simpa using mul_le_mul_of_nonneg_left (hf y) (prob_nonneg hD hp hp1 x y)

theorem maximum_neighbor {p : ℝ} (hD : 0 < D) (hp : 0 < p) (hp1 : p ≤ 1)
    {f : Site D → ℝ} (hf : ∀ x, f x ≤ 1) {x y : Site D}
    (hx : rowMean p f x = 1) (hy : y ∈ neighbors x) : f y = 1 := by
  have hpos : 0 < prob p x y := by
    simpa [transition] using transition_pos_of_neighbor hp hy
  have hz : ∑ z ∈ insert x (neighbors x), prob p x z * (1 - f z) = 0 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, row_one hD hp hp1]
    change 1 - rowMean p f x = 0
    rw [hx, sub_self]
  have hh := Finset.single_le_sum (s:=insert x (neighbors x))
    (f:=fun z => prob p x z * (1 - f z)) (fun z _ => mul_nonneg (prob_nonneg hD hp hp1 _ _) (sub_nonneg.mpr (hf z))) (Finset.mem_insert_of_mem hy)
  rw [hz] at hh
  nlinarith [hf y]

/-- If return before absorption had probability one, the hitting potential
would equal one along every lattice path, contradicting its zero at a target. -/
theorem first_return_lt_one {p : ℝ} (hD : 0 < D) (hp : 0 < p) (hp1 : p ≤ 1)
    {A : Set (Site D)} {a : Site D} (ha : a ∉ A) (hA : A.Nonempty) :
    rowMean p (hit p a A) a < 1 := by
  let f := hit p a A
  have bound : ∀ x, f x ≤ 1 := fun x => (hit_bounds hD hp hp1 _ _ x).2
  refine lt_of_le_of_ne (rowMean_le_one hD hp hp1 bound a) ?_
  intro e
  obtain ⟨b,hb⟩ := hA
  have prop (x : Site D) (path : Path a x) : f x = 1 := by
    induction path with
    | refl => exact hit_at _ _ _
    | @tail x y path hxy ih =>
      apply maximum_neighbor hD hp hp1 bound _ hxy
      by_cases hxa : x = a
      · simpa [hxa] using e
      · have hxn : x ∉ A := by
          intro hx
          have z := hit_target p ha hx
          exact zero_ne_one (z.symm.trans ih)
        exact (hit_harmonic hD hp hp1 ha hxn hxa).symm.trans ih
  exact zero_ne_one ((hit_target p ha hb).symm.trans (prop b (lattice_path a b)))

end Metropolis.Lattice
end
