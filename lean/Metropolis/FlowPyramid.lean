import Metropolis.FlowLayer
import Metropolis.FlowUpperStatement
import Metropolis.AsymptoticEnergy

noncomputable section
namespace Metropolis.Flow
open Metropolis.Lattice

def nilBatch (D : ℕ) : Batch D where
  Index := Empty
  finite := inferInstance
  key := Empty.elim
  distinct := by intro i; exact i.elim
  current := Empty.elim

private def cost (k n : ℕ) (p : ℝ) := p⁻¹^(k+1) / ((k:ℝ)+1)^n
private def factor (n : ℕ) : ℝ := 2*((n:ℝ)+1)*(1+n)

private theorem pyramid (p : ℝ) (hp : 0 < p) (n k : ℕ) :
    ∃ b : Batch (n+1), (∀ e, rank (b.key e) < 2*(k:ℤ)) ∧
      (∀ f, work b f = f 0 - layerMean k n k f) ∧
      energy p b ≤ factor n * ∑ j ∈ Finset.range k, cost j n p := by
  induction k with
  | zero =>
    refine ⟨nilBatch _,fun e => Empty.elim e,?_,?_⟩
    · intro f
      simp [nilBatch,work,layerMean,mean_zero,show (Fin.cons (0:ℤ) (0 : Site n) : Site (n+1)) = 0 from
        funext fun i => Fin.cases rfl (fun _ => rfl) i]
      exact Finset.sum_empty
    · simp [nilBatch,energy]
      exact (Finset.sum_empty).le
  | succ k ih =>
    obtain ⟨b,rankb,workb,energyb⟩ := ih
    have h₁ : ∀ i j, b.key i ≠ (forward k n).key j := by
      intro i j h
      have ht := congrArg rank h
      rw [forward_rank] at ht
      exact (rankb i).ne ht
    let bf := join b (forward k n) h₁
    have hm (i : bf.Index) : rank (bf.key i) ≤ 2*(k:ℤ) := by
      rcases i with i | j
      · exact (rankb i).le
      · exact (forward_rank k n j).le
    have h₂ : ∀ i j, bf.key i ≠ (lateral k n).key j := by
      intro i j h
      have ht := congrArg rank h
      rw [lateral_rank] at ht
      have := hm i
      omega
    refine ⟨join bf (lateral k n) h₂,?_,?_,?_⟩
    · rintro (i|i)
      · have := hm i
        change rank (bf.key i) < _
        omega
      · change rank ((lateral k n).key i) < _
        rw [lateral_rank]
        omega
    · intro f
      rw [work_join,show work bf f = _ from work_join b _ h₁ f,workb,forward_work,lateral_work]
      ring
    · rw [energy_join,show energy p bf = _ from energy_join p b _ h₁, Finset.sum_range_succ]
      have hv := forward_energy k n p hp
      have hh := lateral_energy k n p hp
      unfold factor cost at *
      push_cast at *
      linarith

theorem face_flow_bound (n : ℕ) {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N → ∃ b : Batch (n+1),
      unitTo (face n N) b ∧ energy p b ≤ C * (p⁻¹^N / (N:ℝ)^n) := by
  obtain ⟨K,hK,hbound⟩ := Asymptotic.energy_sum_bound n hp hp'
  have hfac : 0 < factor n := by unfold factor; positivity
  refine ⟨factor n*K,mul_pos hfac hK,?_⟩
  intro N hN
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  obtain ⟨b,rankb,workb,energyb⟩ := pyramid p hp n k
  have h : ∀ i j, b.key i ≠ (forward k n).key j := by
    intro i j hij
    exact (rankb i).ne ((congrArg rank hij).trans (forward_rank k n j))
  let current := join b (forward k n) h
  have complete : unitTo (face n (k+1)) current := by
    intro f hf
    rw [show work current f = _ from work_join b _ h f,workb,forward_work]
    have hzero : layerMean k n (k+1) f = 0 := by
      unfold layerMean
      rw [← box_mean]
      apply Finset.sum_eq_zero
      intro z _
      rw [hf _ (by exact ⟨by simp,fun i => by simpa using coords_bound k n z i⟩),mul_zero]
    rw [hzero]
    ring
  refine ⟨current,complete,?_⟩
  calc energy p current ≤ factor n * ∑ j ∈ Finset.range (k+1), cost j n p := by
         rw [show energy p current = _ from energy_join p b _ h,Finset.sum_range_succ]
         have hv := forward_energy k n p hp
         have hc : 0 ≤ cost k n p := by unfold cost; positivity
         have hdiff : 2*((n:ℝ)+1) ≤ factor n := by
           unfold factor
           nlinarith [sq_nonneg (n:ℝ),Nat.cast_nonneg (α:=ℝ) n]
         push_cast at hv
         rw [mul_add]
         exact add_le_add energyb (hv.trans (mul_le_mul_of_nonneg_right hdiff hc))
       _ ≤ _ := by
         rw [mul_assoc]
         exact mul_le_mul_of_nonneg_left (hbound (k+1) (by omega)) hfac.le

theorem resistance_upper : UpperStatement := by
  intro D hD p hp hp'
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : D ≠ 0)
  obtain ⟨C,hC,h⟩ := face_flow_bound n hp hp'
  refine ⟨C,hC,?_⟩
  intro N hN
  obtain ⟨b,hb,he⟩ := h N hN
  exact (resistance_le hp b hb).trans he

end Metropolis.Flow
