import Metropolis.HitPotential
import Metropolis.Mass

open scoped ENNReal
noncomputable section
namespace Metropolis.Lattice
/-- Statement of Lemma 1 for the infinite lattice, a finite target and
the path-measure probabilities specified by the discrete transition kernel. -/
def HittingStatement : Prop :=
  ∀ (D : ℕ), 0 < D → ∀ p : ℝ, 0 < p → p < 1 →
    ∀ (a : Site D) (A : Set (Site D)), A.Nonempty → A.Finite → a ∉ A →
      let R := (capacity p a A)⁻¹
      let M := ∑' x : Site D, ENNReal.ofReal (mass p x)
      let H := meanHitting p a A
      M ≠ ∞ ∧ H ≠ ∞ ∧
      H = R * (∑' x, ENNReal.ofReal (mass p x) * Green.entrance (stopped p A) a x) ∧
      ENNReal.ofReal (mass p a) * R ≤ H ∧ H ≤ M * R
end Metropolis.Lattice
end
