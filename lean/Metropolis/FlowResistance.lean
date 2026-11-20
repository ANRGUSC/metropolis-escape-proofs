import Metropolis.Lattice
import Mathlib.Data.Fintype.Sum

noncomputable section
namespace Metropolis.Flow

open Lattice

/-- A finite current extended by zero outside its listed positive-coordinate
edges. Injectivity makes the edge integral count each unoriented edge once. -/
structure Batch (D : ℕ) where
  Index : Type
  finite : Fintype Index
  key : Index → Site D × Fin D
  distinct : Function.Injective key
  current : Index → ℝ

attribute [instance] Batch.finite

def work {D : ℕ} (b : Batch D) (f : Site D → ℝ) : ℝ :=
  ∑ j, b.current j * (f (b.key j).1 - f (step (b.key j).1 (b.key j).2 1))

def energy {D : ℕ} (p : ℝ) (b : Batch D) : ℝ :=
  ∑ j, b.current j ^ 2 / conductance p (b.key j).1 (b.key j).2

/-- Testing conservation against every potential zero on the terminal set
specifies unit injection at the origin and zero divergence off the terminals.
In particular one may test against the indicator of a single vertex. -/
def unitTo {D : ℕ} (target : Set (Site D)) (b : Batch D) : Prop :=
  ∀ f : Site D → ℝ, (∀ x ∈ target, f x = 0) → work b f = f 0

def resistance {D : ℕ} (p : ℝ) (target : Set (Site D)) : ℝ :=
  sInf {E | ∃ b : Batch D, unitTo target b ∧ energy p b = E}

def face (n N : ℕ) : Set (Site (n+1)) :=
  {x | x 0 = (N:ℤ) ∧ ∀ i : Fin n, (x i.succ).natAbs ≤ N-1}

theorem resistance_le {D : ℕ} {p : ℝ} (hp : 0 < p) {target : Set (Site D)}
    (b : Batch D) (hb : unitTo target b) : resistance p target ≤ energy p b := by
  apply csInf_le
  · refine ⟨0,?_⟩
    rintro E ⟨q,_,rfl⟩
    exact Finset.sum_nonneg fun e _ => div_nonneg (sq_nonneg _) (conductance_pos p hp ..).le
  · exact ⟨b,hb,rfl⟩

def join {D : ℕ} (a b : Batch D) (h : ∀ i j, a.key i ≠ b.key j) : Batch D where
  Index := a.Index ⊕ b.Index
  finite := inferInstance
  key := Sum.elim a.key b.key
  current := Sum.elim a.current b.current
  distinct := by
    intro i j hij
    cases i with
    | inl x =>
      cases j with
      | inl y => exact congrArg Sum.inl (a.distinct hij)
      | inr y => exact (h x y hij).elim
    | inr x =>
      cases j with
      | inl y => exact (h y x hij.symm).elim
      | inr y => exact congrArg Sum.inr (b.distinct hij)

theorem work_join {D : ℕ} (a b : Batch D) (h) (f : Site D → ℝ) :
    work (join a b h) f = work a f + work b f := by
  classical
  unfold work
  exact Fintype.sum_sum_type ..

theorem energy_join {D : ℕ} (p : ℝ) (a b : Batch D) (h) :
    energy p (join a b h) = energy p a + energy p b := by
  classical
  unfold energy
  exact Fintype.sum_sum_type ..

end Metropolis.Flow
