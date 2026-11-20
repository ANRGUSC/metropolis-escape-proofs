import Metropolis.DirichletParts

namespace Metropolis.Lattice
open scoped ENNReal
noncomputable section
variable {D : ℕ}

private def clip (t : ℝ) : ℝ := max 0 (min 1 t)

private theorem clipped_unit (f : Site D → ℝ) : inUnit (fun x => clip (f x)) :=
  fun x => ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

private theorem clip_diff (s t : ℝ) : |clip s-clip t| ≤ |s-t| := by
  have hmin : |min 1 s-min 1 t| ≤ |s-t| := by
    simpa using abs_min_sub_min_le_max 1 s 1 t
  have hmax : |clip s-clip t| ≤ |min 1 s-min 1 t| := by
    simpa [clip] using abs_max_sub_max_le_max 0 (min 1 s) 0 (min 1 t)
  exact hmax.trans hmin

private theorem clip_energy {p : ℝ} (hp : 0 < p) (f : Site D → ℝ) :
    dirichlet p (fun x => clip (f x)) ≤ dirichlet p f := by
  apply ENNReal.tsum_le_tsum
  rintro ⟨x,i⟩
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_left _ (conductance_pos p hp x i).le
  simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (clip_diff (f x) (f (step x i 1))) 2

private theorem dirichlet_as_mixed {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hm : Summable (mass (D:=D) p)) {h : Site D → ℝ} (hb : inUnit h) :
    dirichlet p h = ENNReal.ofReal (∑' e, mixed p h h e) := by
  have hs := summable_mixed hp hp1 hm hb hb
  have hn (e : Bond D) : 0 ≤ mixed p h h e := by
    unfold mixed currentDiff
    rw [mul_assoc, ← sq]
    exact mul_nonneg (conductance_pos p hp _ _).le (sq_nonneg _)
  rw [ENNReal.ofReal_tsum_of_nonneg hn hs]
  apply tsum_congr
  intro e
  simp [mixed,currentDiff,pow_two,mul_assoc]

/-- The hitting-probability potential attains the Dirichlet minimum and its
energy is the source mass times the first-step escape probability. -/
theorem harmonic_capacity {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hm : Summable (mass (D:=D) p)) (a : Site D) (A : Set (Site D)) (h : Site D → ℝ)
    (hb : inUnit h) (ha : h a = 1) (hA : ∀ x ∈ A, h x = 0)
    (harm : ∀ x, x ≠ a → x ∉ A → h x = edgeRowMean p h x) :
    capacity p a A = ENNReal.ofReal (mass p a * (1-edgeRowMean p h a)) := by
  have boundary (g : Site D → ℝ) (gb : inUnit g) (ga : g a = 1)
      (gA : ∀ x ∈ A, g x = 0) :
      ∑' e, mixed p h g e = mass p a*(1-edgeRowMean p h a) := by
    rw [integration_by_parts hp hp1 hm hb gb, tsum_eq_single a]
    · rw [ha,ga,mul_one]
    · intro x hx
      by_cases hxa : x ∈ A
      · simp [gA x hxa]
      · simp [harm x hx hxa]
  have eh := boundary h hb ha hA
  apply le_antisymm
  · exact (capacity_le_test p a A h ha hA).trans_eq ((dirichlet_as_mixed hp hp1 hm hb).trans (congrArg ENNReal.ofReal eh))
  · unfold capacity
    refine le_iInf fun f => le_iInf fun fa => le_iInf fun fA => ?_
    let g := fun x => clip (f x)
    have gb : inUnit g := clipped_unit f
    have ga : g a = 1 := by simp [g,clip,fa]
    have gA : ∀ x ∈ A, g x=0 := fun x hx => by simp [g,clip,fA x hx]
    apply le_trans _ (clip_energy hp f)
    rw [dirichlet_as_mixed hp hp1 hm gb]
    apply ENNReal.ofReal_le_ofReal
    have hh := summable_mixed hp hp1 hm hb hb
    have hg := summable_mixed hp hp1 hm hb gb
    have gg := summable_mixed hp hp1 hm gb gb
    have quad (e : Bond D) : 2*mixed p h g e - mixed p h h e ≤ mixed p g g e := by
      unfold mixed currentDiff
      have hc := (conductance_pos p hp e.1 e.2).le
      nlinarith only [mul_nonneg hc (sq_nonneg
        ((h e.1-h (step e.1 e.2 1)) - (g e.1-g (step e.1 e.2 1))))]
    have le := ((hg.mul_left 2).sub hh).tsum_le_tsum quad gg
    rw [(hg.mul_left 2).tsum_sub hh, tsum_mul_left, boundary g gb ga gA, eh] at le
    linarith

end
end Metropolis.Lattice
