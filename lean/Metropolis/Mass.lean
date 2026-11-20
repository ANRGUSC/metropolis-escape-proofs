import Metropolis.Lattice
import Metropolis.AsymptoticKernel
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.Fintype.BigOperators

open scoped ENNReal
namespace Metropolis.Lattice
noncomputable section
variable {D : ℕ}

theorem coord_bounds (x : Site D) (i : Fin D) :
    -(level x : ℤ) ≤ x i ∧ x i ≤ level x := by
  have hn : (x i).natAbs ≤ level x := Finset.le_sup (s:=Finset.univ) (f:=fun j => (x j).natAbs) (Finset.mem_univ i)
  have hz : |x i| ≤ (level x : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hn
  exact abs_le.mp hz

abbrev Box (D k : ℕ) := Fin D → Fin (2*k+1)
def boxCode (x : Site D) : Σ k, Box D k := ⟨level x, fun i =>
  ⟨(x i + (level x:ℤ)).toNat, by have h := coord_bounds x i; omega⟩⟩
def boxDecode (z : Σ k, Box D k) : Site D := fun i => ((z.2 i).val : ℤ) - z.1

theorem boxCode_injective : Function.Injective (boxCode (D:=D)) := by
  apply Function.LeftInverse.injective (g:=boxDecode)
  intro x; funext i
  have hi := coord_bounds x i
  change ((x i + (level x:ℤ)).toNat : ℤ) - level x = x i
  omega

theorem total_mass_ne_top {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (∑' x : Site D, ENNReal.ofReal (mass p x)) ≠ ∞ := by
  apply ne_of_lt
  let value : (Σ k, Box D k) → ℝ≥0∞ := fun z => ENNReal.ofReal (p^z.1)
  calc
    _ ≤ ∑' z, value z := ENNReal.tsum_comp_le_tsum_of_injective boxCode_injective value
    _ = ∑' k : ℕ, ENNReal.ofReal (((2*k+1:ℕ):ℝ)^D * p^k) := by
      rw [ENNReal.tsum_sigma']
      apply tsum_congr; intro k
      rw [ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg _) D), ENNReal.ofReal_pow (Nat.cast_nonneg _) D, ENNReal.ofReal_natCast]
      simp [value, Box, tsum_fintype]
    _ ≤ ∑' k, ENNReal.ofReal ((2:ℝ)^D * Metropolis.Asymptotic.weight D p k) := by
      apply ENNReal.tsum_le_tsum
      intro k; apply ENNReal.ofReal_le_ofReal
      unfold Metropolis.Asymptotic.weight
      rw [← mul_assoc, ← mul_pow]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp.le _)
      apply pow_le_pow_left₀ (by positivity); push_cast; linarith
    _ < ∞ := lt_top_iff_ne_top.mpr (((Metropolis.Asymptotic.weight_summable D hp hp1).mul_left _).tsum_ofReal_ne_top)
end
end Metropolis.Lattice
