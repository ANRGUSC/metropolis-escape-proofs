import Metropolis.DirichletMinimum
import Metropolis.HitPotential

namespace Metropolis.Lattice

/-- Dirichlet's principle for a bounded harmonic potential of the walk. -/
theorem capacity_of_harmonic {D : ℕ} {p : ℝ} (_hD : 0 < D) (hp : 0 < p) (hp1 : p < 1)
    (hsum : Summable (mass p : Site D → ℝ)) {A : Set (Site D)} {a : Site D}
    (_ha : a ∉ A) (f : Site D → ℝ) (bounds : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (fa : f a = 1) (fA : ∀ x ∈ A, f x = 0)
    (harm : ∀ x, x ∉ A → x ≠ a → f x = rowMean p f x) :
    capacity p a A = ENNReal.ofReal (mass p a * (1-rowMean p f a)) :=
  harmonic_capacity hp hp1.le hsum a A f bounds fa fA (fun x hx hxA => harm x hxA hx)

#print axioms capacity_of_harmonic
end Metropolis.Lattice
