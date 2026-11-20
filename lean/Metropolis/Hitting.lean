import Metropolis.HittingAssembly
import Metropolis.Diagonal
import Metropolis.Dirichlet

open scoped ENNReal
noncomputable section
namespace Metropolis.Lattice

theorem hitting_capacity : HittingStatement := by
  intro D hD p hp hp1 a A hA _hFin ha
  have total := total_mass_ne_top (D:=D) hp hp1
  have hs : Summable (mass p : Site D → ℝ) := by
    have hs' := ENNReal.summable_toReal total
    simpa [ENNReal.toReal_ofReal (mass_pos p hp _).le] using hs'
  have cap := capacity_of_harmonic hD hp hp1 hs ha (hit p a A)
    (hit_bounds hD hp hp1.le A a) (hit_at p A a) (fun _ hx => hit_target p ha hx)
    (fun _ hx hne => hit_harmonic hD hp hp1.le ha hx hne)
  exact ⟨total, hitting_from_capacity hD hp hp1 ha (first_return_lt_one hD hp hp1.le ha hA)
    (diagonal_visits hD hp hp1.le ha hA) cap⟩

theorem meanHitting_le_mass_resistance {D : ℕ} {p : ℝ} {A : Set (Site D)} {a : Site D}
    (hD : 0 < D) (hp : 0 < p) (hp1 : p < 1) (hA : A.Nonempty) (hFin : A.Finite) (ha : a ∉ A) :
    meanHitting p a A ≤ (∑' x : Site D, ENNReal.ofReal (mass p x)) * (capacity p a A)⁻¹ :=
  (hitting_capacity D hD p hp hp1 a A hA hFin ha).2.2.2.2

#print axioms hitting_capacity
end Metropolis.Lattice
end
