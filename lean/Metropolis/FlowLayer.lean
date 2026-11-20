import Metropolis.FlowMean
import Metropolis.FlowResistance
import Mathlib.Algebra.BigOperators.Field
noncomputable section
namespace Metropolis.Flow
open Metropolis.Lattice Cube

def forward (k n : ℕ) : Batch (n+1) where
  Index := Box k n
  finite := inferInstance
  key z := (Fin.cons (k:ℤ) (coords k n z),0)
  current _ := ((2*(k:ℝ)+1)⁻¹)^n
  distinct := by
    intro z w h
    apply coords_injective
    ext i
    exact congrFun (Prod.mk.inj h).1 i.succ

def lateral (k n : ℕ) : Batch (n+1) where
  Index := Edge k n
  finite := inferInstance
  key e := (Fin.cons ((k:ℤ)+1) (cubeCoords k n (edgeFrom k n e)),(direction k n e).succ)
  current := cubeFlow k n
  distinct := by
    intro e d h
    obtain ⟨hx,hi⟩ := Prod.mk.inj h
    apply edge_index_injective
    apply Prod.ext _ (Fin.succ_inj.mp hi)
    apply cubeCoords_injective
    exact funext fun i => congrFun hx i.succ

def rank {n : ℕ} (e : Site (n+1) × Fin (n+1)) : ℤ :=
  2 * e.1 0 - if e.2 = 0 then 0 else 1

theorem forward_rank (k n : ℕ) (z : (forward k n).Index) :
    rank ((forward k n).key z) = 2*(k:ℤ) := by simp [rank,forward]

theorem lateral_rank (k n : ℕ) (e : (lateral k n).Index) :
    rank ((lateral k n).key e) = 2*(k:ℤ)+1 := by simp [rank,lateral]; ring

def layerMean (r n t : ℕ) (f : Site (n+1) → ℝ) : ℝ :=
  mean r n (fun z => f (Fin.cons (t:ℤ) z))

theorem forward_work (k n : ℕ) (f : Site (n+1) → ℝ) :
    work (forward k n) f = layerMean k n k f - layerMean k n (k+1) f := by
  simp only [work,forward,step_first,mul_sub,Finset.sum_sub_distrib]
  unfold layerMean
  push_cast
  rw [← box_mean,← box_mean]
  rfl

theorem lateral_work (k n : ℕ) (f : Site (n+1) → ℝ) :
    work (lateral k n) f = layerMean k n (k+1) f - layerMean (k+1) n (k+1) f := by
  simp only [work,lateral,step_tail,edge_endpoint]
  let g : Vertex k n → ℝ := fun z => f (Fin.cons ((k:ℤ)+1) (cubeCoords k n z))
  change (∑ e, cubeFlow k n e * (g (edgeFrom k n e) - g (edgeTo k n e))) = _
  rw [← cube_parts]
  simp only [cube_balance,sub_mul,Finset.sum_sub_distrib,g]
  unfold layerMean
  push_cast
  rw [← inner_mean,← outer_mean]

theorem forward_energy (k n : ℕ) (p : ℝ) (hp : 0 < p) :
    energy p (forward k n) ≤ 2*(n+1:ℕ) * (p⁻¹^(k+1) / ((k:ℝ)+1)^n) := by
  have hcond (z : Box k n) : conductance p (Fin.cons (k:ℤ) (coords k n z)) 0 =
      p^(k+1) / (2*(n+1:ℕ)) := by
    unfold conductance
    rw [step_first,level_cons k _ (coords_bound k n z)]
    have hnext := level_cons (k+1) _ (fun i => (coords_bound k n z i).trans (Nat.le_succ _))
    push_cast at hnext
    rw [hnext,max_eq_right (Nat.le_succ _)]
  change (∑ z : Box k n, (((2*(k:ℝ)+1)⁻¹)^n)^2 /
    conductance p (Fin.cons (k:ℤ) (coords k n z)) 0) ≤ _
  simp only [hcond,Finset.sum_const,Finset.card_univ,box_card,nsmul_eq_mul]
  push_cast
  have hpos : (0:ℝ)<2*k+1 := by positivity
  have hs : ((k:ℝ)+1)^n ≤ (2*k+1)^n := by
    apply pow_le_pow_left₀ (by positivity); linarith [Nat.cast_nonneg (α:=ℝ) k]
  calc
    _ = 2*((n:ℝ)+1) * (p⁻¹^(k+1)/(2*(k:ℝ)+1)^n) := by
      simp only [inv_pow]
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (by positivity) (by positivity) hs) (by positivity)

theorem lateral_energy (k n : ℕ) (p : ℝ) (hp : 0 < p) :
    energy p (lateral k n) ≤ 2*(n+1:ℕ)*(n:ℝ) * (p⁻¹^(k+1) / ((k:ℝ)+1)^n) := by
  have hc (e : Edge k n) : conductance p
      (Fin.cons ((k:ℤ)+1) (cubeCoords k n (edgeFrom k n e))) (direction k n e).succ =
      p^(k+1) / (2*(n+1:ℕ)) := by
    unfold conductance
    rw [step_tail,edge_endpoint]
    have ha := level_cons (k+1) _ (cubeCoords_bound k n (edgeFrom k n e))
    have hb := level_cons (k+1) _ (cubeCoords_bound k n (edgeTo k n e))
    push_cast at ha hb
    rw [ha,hb,max_self]
  change (∑ e : Edge k n, cubeFlow k n e ^ 2 / conductance p
    (Fin.cons ((k:ℤ)+1) (cubeCoords k n (edgeFrom k n e))) (direction k n e).succ) ≤ _
  simp only [hc]
  rw [← Finset.sum_div,← edge_sum,div_div_eq_mul_div,inv_pow]
  have H := cube_energy k n
  rw [inv_pow,← div_eq_mul_inv] at H
  calc
    _ ≤ ((n:ℝ)/((k:ℝ)+1)^n * (2*(n+1:ℕ))) / p^(k+1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right H (by positivity)) (by positivity)
    _ = _ := by ring

end Metropolis.Flow
