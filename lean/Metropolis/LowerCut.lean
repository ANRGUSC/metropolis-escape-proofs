import Metropolis.LowerGeometry
import Metropolis.Capacity
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Finset
open scoped ENNReal

namespace Metropolis.Lower
open Metropolis.Lattice

/-- The equilibrium-potential competitor that drops across the final shell. -/
def cubeTest {D : ℕ} (k : ℕ) (x : Site D) : ℝ := if level x ≤ k then 1 else 0

private noncomputable def edgeBound (d k : ℕ) (p : ℝ) : ℝ :=
  p^(k+1) / (2 * ((d+1:ℕ):ℝ))

private theorem cut_dominates (d k : ℕ) {p : ℝ} (hp : 0 < p) (hp' : p ≤ 1)
    (e : Site (d+1) × Fin (d+1)) :
    ENNReal.ofReal (conductance p e.1 e.2 * (cubeTest k e.1 - cubeTest k (step e.1 e.2 1))^2) ≤
      ∑ f : FaceIndex d k, if faceEdge d k f = e then ENNReal.ofReal (edgeBound d k p) else 0 := by
  classical
  obtain ⟨x,i⟩ := e
  by_cases hx : level x ≤ k <;> by_cases hy : level (step x i 1) ≤ k
  · simp [cubeTest,hx,hy]
  · obtain ⟨f,hf⟩ := edge_of_crossing x i (Or.inl ⟨hx,hy⟩)
    apply le_trans _ (single_le_sum (f := fun f : FaceIndex d k =>
      if faceEdge d k f = (x,i) then ENNReal.ofReal (edgeBound d k p) else 0)
      (fun _ _ => zero_le) (mem_univ f))
    simp only [hf, if_true, cubeTest, hx, hy, if_false, sub_zero, one_pow, mul_one]
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply pow_le_pow_of_le_one hp.le hp'
    exact le_trans (by omega) (le_max_right _ _)
  · obtain ⟨f,hf⟩ := edge_of_crossing x i (Or.inr ⟨hx,hy⟩)
    apply le_trans _ (single_le_sum (f := fun f : FaceIndex d k =>
      if faceEdge d k f = (x,i) then ENNReal.ofReal (edgeBound d k p) else 0)
      (fun _ _ => zero_le) (mem_univ f))
    simp only [hf, if_true, cubeTest, hx, hy, if_false, zero_sub, even_two.neg_pow, one_pow, mul_one]
    apply ENNReal.ofReal_le_ofReal
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply pow_le_pow_of_le_one hp.le hp'
    exact le_trans (by omega) (le_max_left _ _)
  · simp [cubeTest,hx,hy]

theorem dirichlet_cubeTest (d k : ℕ) {p : ℝ} (hp : 0 < p) (hp' : p ≤ 1) :
    dirichlet p (cubeTest (D:=d+1) k) ≤ ENNReal.ofReal (p^(k+1) * (2*(k:ℝ)+1)^d) := by
  classical
  let w := ENNReal.ofReal (edgeBound d k p)
  calc dirichlet p (cubeTest (D:=d+1) k)
      ≤ ∑' e, ∑ f : FaceIndex d k, if faceEdge d k f = e then w else 0 :=
        ENNReal.tsum_le_tsum (cut_dominates d k hp hp')
    _ = ∑' e, ∑' f : FaceIndex d k, if faceEdge d k f = e then w else 0 := by
        simp [tsum_fintype]
    _ = ∑' f : FaceIndex d k, ∑' e, if faceEdge d k f = e then w else 0 :=
        ENNReal.tsum_comm
    _ = (Fintype.card (FaceIndex d k) : ℝ≥0∞) * w := by simp [tsum_fintype]
    _ = _ := by
      have hw : 0 ≤ edgeBound d k p := by unfold edgeBound; positivity
      have count : Fintype.card (FaceIndex d k) = (d+1)*2*(2*k+1)^d := by
        simp [FaceIndex, Fintype.card_pi, mul_assoc]
      rw [count]
      dsimp [w]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      unfold edgeBound
      push_cast
      field_simp

/-- Upper bound on the true lattice capacity given by the last-shell cut. -/
theorem capacity_last_cut (d k : ℕ) {p : ℝ} (hp : 0 < p) (hp' : p ≤ 1) :
    capacity p (0 : Site (d+1)) {x | level x = k+1} ≤
      ENNReal.ofReal (p^(k+1) * (2*(k:ℝ)+1)^d) := by
  apply (capacity_le_test _ _ _ (cubeTest k) (by simp [cubeTest]) ?_).trans
    (dirichlet_cubeTest d k hp hp')
  intro x hx
  change level x = k+1 at hx
  simp [cubeTest, hx]

end Metropolis.Lower
