import Metropolis.Lattice
import Metropolis.TransportProduct
import Mathlib.Data.Fin.Tuple.Basic

noncomputable section
namespace Metropolis.Flow

open Metropolis.Lattice Cube

/-- Ordered tuples over a finite coordinate interval, including radius zero. -/
def Box (r : ℕ) : ℕ → Type
  | 0 => Unit
  | n+1 => Fin (2*r+1) × Box r n

instance boxFinite (r : ℕ) : (n : ℕ) → Fintype (Box r n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => letI := boxFinite r n; inferInstanceAs (Fintype (_ × Box r n))

instance cubeFinite (k : ℕ) : (n : ℕ) → Fintype (Vertex k n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n+1 => letI := cubeFinite k n; inferInstanceAs (Fintype (_ × Vertex k n))

instance edgeFinite (k : ℕ) : (n : ℕ) → Fintype (Edge k n)
  | 0 => inferInstanceAs (Fintype Empty)
  | n+1 => letI := edgeFinite k n; inferInstanceAs (Fintype ((_ × Vertex k n) ⊕ (_ × Edge k n)))

def coords (r : ℕ) : (n : ℕ) → Box r n → Site n
  | 0, _ => 0
  | n+1, (x,z) => Fin.cons ((x.val:ℤ)-r) (coords r n z)

def cubeCoords (k : ℕ) : (n : ℕ) → Vertex k n → Site n
  | 0, _ => 0
  | n+1, (x,z) => Fin.cons ((x.val:ℤ)-(k+1)) (cubeCoords k n z)

theorem coords_injective (r n : ℕ) : Function.Injective (coords r n) := by
  induction n with
  | zero => intro x y _; exact Subsingleton.elim (α:=Unit) x y
  | succ n ih =>
    rintro ⟨x,z⟩ ⟨y,w⟩ h
    have a := congrFun h 0
    have b := fun i : Fin n => congrFun h i.succ
    simp only [coords,Fin.cons_zero,Fin.cons_succ] at a b
    have hxy : x.val = y.val := by exact_mod_cast sub_left_inj.mp a
    exact Prod.ext (Fin.ext hxy) (ih (funext b))

theorem cubeCoords_injective (k n : ℕ) : Function.Injective (cubeCoords k n) := by
  induction n with
  | zero => intro x y _; exact Subsingleton.elim (α:=Unit) x y
  | succ n ih =>
    rintro ⟨x,z⟩ ⟨y,w⟩ h
    have a := congrFun h 0
    have b := fun i : Fin n => congrFun h i.succ
    simp only [cubeCoords,Fin.cons_zero,Fin.cons_succ] at a b
    have hxy : x.val = y.val := by exact_mod_cast sub_left_inj.mp a
    exact Prod.ext (Fin.ext hxy) (ih (funext b))

theorem coords_bound (r n : ℕ) (z : Box r n) (i : Fin n) : ((coords r n z) i).natAbs ≤ r := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    obtain ⟨x,z⟩ := z
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [coords,Fin.cons_zero]
      have := x.isLt
      omega
    · simpa only [coords,Fin.cons_succ] using ih z j

theorem cubeCoords_bound (k n : ℕ) (z : Vertex k n) (i : Fin n) :
    ((cubeCoords k n z) i).natAbs ≤ k+1 := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    obtain ⟨x,z⟩ := z
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [cubeCoords,Fin.cons_zero]
      have := x.isLt
      omega
    · simpa only [cubeCoords,Fin.cons_succ] using ih z j

theorem level_cons {n : ℕ} (t : ℕ) (z : Site n) (hz : ∀ i, (z i).natAbs ≤ t) :
    level (Fin.cons (t:ℤ) z : Site (n+1)) = t := by
  apply le_antisymm
  · apply Finset.sup_le
    intro i _
    exact Fin.cases (by simp) (fun j => by simpa using hz j) i
  · simpa [level] using (Finset.le_sup (s:=Finset.univ)
      (f:=fun i : Fin (n+1) => ((Fin.cons (t:ℤ) z : Site (n+1)) i).natAbs) (Finset.mem_univ 0))

theorem step_first {n : ℕ} (t : ℤ) (z : Site n) :
    step (Fin.cons t z : Site (n+1)) 0 1 = Fin.cons (t+1) z := by
  funext i
  exact Fin.cases (by simp [step]) (fun j => by simp [step,Function.update_of_ne]) i

theorem step_tail {n : ℕ} (t : ℤ) (z : Site n) (i : Fin n) :
    step (Fin.cons t z : Site (n+1)) i.succ 1 = Fin.cons t (step z i 1) := by
  funext j
  refine Fin.cases (by simp [step,Function.update_of_ne (Fin.succ_ne_zero i).symm]) (fun l => ?_) j
  by_cases h : l = i
  · subst l; simp [step]
  · simp [step,Function.update_of_ne,h]

theorem box_card (r n : ℕ) : Fintype.card (Box r n) = (2*r+1)^n := by
  induction n with
  | zero => exact Fintype.card_unique (α:=Unit)
  | succ n ih =>
    change Fintype.card (Fin (2*r+1) × Box r n) = _
    rw [Fintype.card_prod,Fintype.card_fin,ih,pow_succ']

end Metropolis.Flow
