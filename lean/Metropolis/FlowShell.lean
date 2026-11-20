import Metropolis.FlowBox
import Metropolis.FlowResistance
import Metropolis.LowerGeometry
import Mathlib.Data.Set.Finite.Range
noncomputable section
namespace Metropolis.Flow
open Metropolis.Lattice

theorem finite_shell (D N : ℕ) : ({x : Site D | level x = N} : Set (Site D)).Finite := by
  let decode (z : Fin D → Fin (2*N+1)) : Site D := fun i => ((z i).val:ℤ)-N
  apply (Set.finite_range decode).subset
  intro x hx
  have bounds := (Lower.level_le_iff x N).mp (le_of_eq hx)
  let z : Fin D → Fin (2*N+1) := fun i => ⟨(x i + N).toNat,by have := bounds i; omega⟩
  refine ⟨z,?_⟩
  funext i
  change ((x i + (N:ℤ)).toNat:ℤ)-N = x i
  have := bounds i
  omega

theorem nonempty_shell (n N : ℕ) : ({x : Site (n+1) | level x = N} : Set _).Nonempty := by
  refine ⟨Fin.cons (N:ℤ) (0 : Site n),level_cons N _ ?_⟩
  simp

theorem face_subset_shell (n N : ℕ) : face n N ⊆ {x | level x = N} := by
  rintro x ⟨hx,hy⟩
  have b : ∀ i : Fin n, (x i.succ).natAbs ≤ N := fun i => (hy i).trans (Nat.sub_le _ _)
  have eq : (Fin.cons (N:ℤ) (fun i => x i.succ) : Site (n+1)) = x := by
    funext i
    exact Fin.cases (by simpa using hx.symm) (fun _ => by simp) i
  change level x = N
  rw [← eq]
  exact level_cons N _ b

theorem unitTo_mono {D : ℕ} {A B : Set (Site D)} {b : Batch D} (hab : A ⊆ B)
    (h : unitTo A b) : unitTo B b := fun f hf => h f (fun x hx => hf x (hab hx))

end Metropolis.Flow
