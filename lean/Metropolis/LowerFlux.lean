import Metropolis.LowerFluxDefs
import Metropolis.LowerCut
import Metropolis.Walk

open scoped ENNReal
open Finset
namespace Metropolis.Lower
open Metropolis.Lattice
noncomputable section
variable {D : ℕ}

private def oriented (k : ℕ) (e : Site D × Fin D) : Site D × Site D :=
  if level e.1 ≤ k then (e.1, step e.1 e.2 1) else (step e.1 e.2 1, e.1)

private def edgeEnergy (p : ℝ) (k : ℕ) (e : Site D × Fin D) : ℝ≥0∞ :=
  ENNReal.ofReal (conductance p e.1 e.2 *
    (cubeTest k e.1 - cubeTest k (step e.1 e.2 1))^2)

private def fluxTerm (p : ℝ) (k : ℕ) (q : Site D × Site D) : ℝ≥0∞ :=
  if level q.1 ≤ k ∧ ¬level q.2 ≤ k then ENNReal.ofReal (mass p q.1) * transition p q.1 q.2 else 0

private theorem flux_pairs (p : ℝ) (k : ℕ) :
    stationaryExit (transition (D:=D) p) (fun x => ENNReal.ofReal (mass p x)) {x | ¬level x ≤ k} =
      ∑' q : Site D × Site D, fluxTerm p k q := by
  classical
  rw [ENNReal.tsum_prod']
  apply tsum_congr
  intro x
  by_cases hx : level x ≤ k
  · simp only [exitRow, Set.mem_ofPred_eq, if_neg (not_not_intro hx),
      ← ENNReal.tsum_mul_left] at *
    apply tsum_congr
    intro y
    by_cases hy : level y ≤ k <;> simp [fluxTerm,hx,hy]
  · simp [exitRow,fluxTerm,hx]

private theorem adjacent_weight {p : ℝ} (hp : 0 < p) (x y : Site D) (ne : x ≠ y)
    (hn : y ∈ neighbors x) :
    ENNReal.ofReal (mass p x) * transition p x y = ENNReal.ofReal (edgeMass p x y) := by
  rw [transition, ← ENNReal.ofReal_mul (mass_pos p hp x).le]
  congr 1
  simp only [prob, if_neg ne, move, if_pos hn]
  field_simp [(mass_pos p hp x).ne']

private theorem pair_bound {p : ℝ} (hp : 0 < p) (k : ℕ) (q : Site D × Site D) :
    fluxTerm p k q ≤ ∑' e : Site D × Fin D, if oriented k e = q then edgeEnergy p k e else 0 := by
  classical
  obtain ⟨x,y⟩ := q
  by_cases h : level x ≤ k ∧ ¬level y ≤ k
  · have hne : x ≠ y := by rintro rfl; exact h.2 h.1
    rw [fluxTerm, if_pos h]
    by_cases hn : y ∈ neighbors x
    · rw [adjacent_weight hp x y hne hn]
      obtain ⟨⟨i,b⟩,_,he⟩ := Finset.mem_image.mp hn
      cases b with
      | true =>
        have hy : step x i 1 = y := he
        apply le_trans _ (ENNReal.le_tsum (f:=fun e : Site D × Fin D =>
          if oriented k e = (x,y) then edgeEnergy p k e else 0) (x,i))
        simp [oriented, h.1, hy, edgeEnergy, conductance, edgeMass, cubeTest, h.2]
      | false =>
        have hy : step x i (-1) = y := he
        have hx : step y i 1 = x := by rw [← hy]; exact step_cancel x i (-1)
        apply le_trans _ (ENNReal.le_tsum (f:=fun e : Site D × Fin D =>
          if oriented k e = (x,y) then edgeEnergy p k e else 0) (y,i))
        simp [oriented, h.2, hx, edgeEnergy, conductance, edgeMass, cubeTest, h.1, max_comm]
    · simp [transition, prob, hne, move, hn]
  · simp only [fluxTerm, if_neg h, zero_le]

/-- Every ordered transition leaving the inner cube appears as exactly one
crossing of an unoriented lattice edge in the test potential's Dirichlet energy. -/
theorem stationaryExit_le_dirichlet (k : ℕ) {p : ℝ} (hp : 0 < p) :
    stationaryExit (transition p) (fun x : Site D => ENNReal.ofReal (mass p x))
      {x | ¬level x ≤ k} ≤ dirichlet p (cubeTest (D:=D) k) := by
  classical
  rw [flux_pairs]
  calc (∑' q : Site D × Site D, fluxTerm p k q) ≤
       ∑' q, ∑' e : Site D × Fin D, if oriented k e = q then edgeEnergy p k e else 0 :=
         ENNReal.tsum_le_tsum (pair_bound hp k)
    _ = ∑' e : Site D × Fin D, ∑' q, if oriented k e = q then edgeEnergy p k e else 0 :=
         ENNReal.tsum_comm
    _ = _ := by simp [dirichlet, edgeEnergy]

end
end Metropolis.Lower
