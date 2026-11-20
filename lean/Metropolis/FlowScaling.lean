import Metropolis.FlowThomson
import Metropolis.FlowPyramid
import Metropolis.FlowShell
import Metropolis.FlowScalingBounds
import Metropolis.LowerStatement

open Filter
open scoped ENNReal Asymptotics
noncomputable section
namespace Metropolis.Flow
open Metropolis.Lattice

/-- Assemble the geometric flow and the occupation-time upper estimate
against the very same target shell as the lower bound. -/
theorem true_scaling_of_hitting_bounds (hLower : Lower.EscapeLowerStatement)
    (massFinite : ∀ (D : ℕ) (p : ℝ), 1 ≤ D → 0 < p → p < 1 →
      (∑' x : Site D, ENNReal.ofReal (mass p x)) ≠ ∞)
    (hHit : ∀ (D : ℕ) (p : ℝ), 1 ≤ D → 0 < p → p < 1 →
      ∀ A : Set (Site D), A.Finite → A.Nonempty → (0 : Site D) ∉ A →
        meanHitting p 0 A ≤ (∑' x : Site D, ENNReal.ofReal (mass p x)) * (capacity p 0 A)⁻¹) :
    TrueScalingStatement := by
  intro D hD p hp hp'
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : D ≠ 0)
  have hD : 1 ≤ n+1 := by omega
  obtain ⟨c,hc,hl⟩ := hLower (n+1) hD p hp hp'
  obtain ⟨C,hC,hflow⟩ := face_flow_bound n hp hp'
  let M := ∑' x : Site (n+1), ENNReal.ofReal (mass p x)
  let s (N : ℕ) := (1/p)^N / (N:ℝ)^n
  have hs (N) : 0 ≤ s N := by dsimp [s]; positivity
  apply theta_of_enclosure _ s hs hc (mul_nonneg (a:=M.toReal) ENNReal.toReal_nonneg hC.le) hl
  intro N hN
  let A : Set (Site (n+1)) := {x | level x = N}
  have hz : (0 : Site (n+1)) ∉ A := by simp [A,show 0 ≠ N by omega]
  obtain ⟨b,hb,he⟩ := hflow N hN
  have cap := weak_thomson hp A b (unitTo_mono (face_subset_shell n N) hb)
  have ht := hHit _ _ hD hp hp' A (finite_shell _ _) (nonempty_shell _ _) hz
  apply ht.trans
  calc M * (capacity p 0 A)⁻¹ ≤ M * ENNReal.ofReal (C*s N) := by
          gcongr
          exact cap.trans (ENNReal.ofReal_le_ofReal (by simpa [s,one_div] using he))
       _ = ENNReal.ofReal (M.toReal * C * s N) := by
          rw [mul_assoc,ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (massFinite _ _ hD hp hp')]

end Metropolis.Flow
