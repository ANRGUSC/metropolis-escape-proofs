import Metropolis.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace Metropolis.Lower
open Metropolis.Lattice

/-- Parallel cut edges are indexed by an axis, one of two faces and the
remaining coordinates in their interval of length 2k+1. -/
abbrev FaceIndex (d k : ℕ) := Fin (d+1) × Bool × (Fin d → Fin (2*k+1))

def faceEdge (d k : ℕ) (f : FaceIndex d k) : Site (d+1) × Fin (d+1) :=
  (f.1.insertNth (if f.2.1 then (k:ℤ) else -(k:ℤ)-1)
      (fun j => (f.2.2 j : ℤ) - k), f.1)

theorem level_le_iff {D : ℕ} (x : Site D) (k : ℕ) :
    level x ≤ k ↔ ∀ i, -(k:ℤ) ≤ x i ∧ x i ≤ (k:ℤ) := by
  simp only [level, Finset.sup_le_iff, Finset.mem_univ, true_implies]
  apply forall_congr'
  intro i
  rw [← Int.ofNat_le, Int.natCast_natAbs, abs_le]

private def encode (k : ℕ) (v : ℤ) (h : -(k:ℤ) ≤ v ∧ v ≤ (k:ℤ)) : Fin (2*k+1) :=
  ⟨(v + k).toNat, by omega⟩

private theorem decode_encode (k : ℕ) (v : ℤ) (h : -(k:ℤ) ≤ v ∧ v ≤ (k:ℤ)) :
    (encode k v h : ℤ) - k = v := by unfold encode; simp; omega

theorem edge_of_crossing {d k : ℕ} (x : Site (d+1)) (i : Fin (d+1))
    (h : (level x ≤ k ∧ ¬ level (step x i 1) ≤ k) ∨
         (¬ level x ≤ k ∧ level (step x i 1) ≤ k)) :
    ∃ f : FaceIndex d k, faceEdge d k f = (x,i) := by
  have oth (j : Fin d) : -(k:ℤ) ≤ x (i.succAbove j) ∧ x (i.succAbove j) ≤ (k:ℤ) := by
    rcases h with h | h
    · exact (level_le_iff x k).mp h.1 _
    · simpa [step, Fin.succAbove_ne] using (level_le_iff _ k).mp h.2 (i.succAbove j)
  have edge : x i = (k:ℤ) ∨ x i = -(k:ℤ)-1 := by
    rcases h with ⟨hx,hy⟩ | ⟨hx,hy⟩
    · left
      have hi := (level_le_iff x k).mp hx i
      by_contra hn
      apply hy
      apply (level_le_iff _ _).mpr
      intro j
      by_cases hj : j=i
      · subst j; simp [step]; omega
      · simpa [step, Function.update_of_ne hj] using (level_le_iff _ _).mp hx j
    · right
      have hi := (level_le_iff _ _).mp hy i
      simp [step] at hi
      by_contra hn
      apply hx
      apply (level_le_iff _ _).mpr
      intro j
      by_cases hj : j=i
      · subst j; omega
      · simpa [step, Function.update_of_ne hj] using (level_le_iff _ _).mp hy j
  let y : Fin d → Fin (2*k+1) := fun j => encode k (x (i.succAbove j)) (oth j)
  have edge_eq (b : Bool) (hb : (if b then (k:ℤ) else -(k:ℤ)-1) = x i) :
      faceEdge d k (i,b,y) = (x,i) := by
    unfold faceEdge
    apply congrArg (fun z : Site (d+1) => (z,i))
    funext j
    refine i.succAboveCases ?_ (fun t => ?_) j
    · simpa [faceEdge] using hb
    · simp [faceEdge, y, decode_encode]
  rcases edge with e|e
  · exact ⟨(i,true,y),edge_eq true e.symm⟩
  · exact ⟨(i,false,y),edge_eq false e.symm⟩

end Metropolis.Lower
