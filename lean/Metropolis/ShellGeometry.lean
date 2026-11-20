import Metropolis.ShellPoisson
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.NormNum

namespace Metropolis.Shell

/-- Coordinates shifted by k identify this box with [-k,k]^D in the integer lattice. -/
abbrev Cube (D k : ℕ) := Fin D → Fin (2*k+1)

def interior {D : ℕ} (k : ℕ) (x : Cube D (k+1)) : Prop :=
  ∀ i, 0 < (x i).val ∧ (x i).val + 1 < 2*(k+1)+1

instance (D k : ℕ) (x : Cube D (k+1)) : Decidable (interior k x) := by
  unfold interior
  infer_instance

/-- Translate a site of the open box by minus one in all coordinates. -/
def interiorEquiv (D k : ℕ) : {x : Cube D (k+1) // interior k x} ≃ Cube D k where
  toFun x i := ⟨(x.1 i).val - 1, by have := (x.2 i).2; omega⟩
  invFun y := ⟨fun i => ⟨(y i).val + 1, by have := (y i).isLt; omega⟩, by
    intro i; have := (y i).isLt; constructor <;> dsimp <;> omega⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    dsimp
    have := (x.2 i).1
    omega
  right_inv y := by funext i; apply Fin.ext; simp

/-- The origin shell has one vertex. Every positive shell is the complement
of the smaller cube inside the larger cube. -/
abbrev ShellSites (D : ℕ) : ℕ → Type
  | 0 => Cube D 0
  | k+1 => {x : Cube D (k+1) // ¬interior k x}

instance shellSiteFintype (D k : ℕ) : Fintype (ShellSites D k) := by
  cases k <;> dsimp [ShellSites] <;> infer_instance

theorem card_shellSites (D k : ℕ) :
    (Fintype.card (ShellSites D k) : ℝ) = shellSize D k := by
  cases k with
  | zero => simp [ShellSites, Cube, shellSize]
  | succ k =>
    change (Fintype.card {x : Cube D (k+1) // ¬interior k x} : ℝ) = _
    rw [Fintype.card_subtype_compl, Fintype.card_congr (interiorEquiv D k)]
    simp only [Cube, Fintype.card_fun, Fintype.card_fin]
    rw [Nat.cast_sub (Nat.pow_le_pow_left (by omega) _)]
    simp [shellSize, Nat.cast_pow]
    ring

/-- Coordinate at the outward face in the chosen signed direction. -/
def endpoint (k : ℕ) (s : Bool) : Fin (2*k+1) :=
  if s then ⟨2*k, by omega⟩ else ⟨0, by omega⟩

abbrev face (d k : ℕ) (i : Fin (d+1)) (s : Bool) :=
  {x : Cube (d+1) k // x i = endpoint k s}

/-- For a crossing in a fixed direction the other d coordinates are free. -/
def faceEquiv (d k : ℕ) (i : Fin (d+1)) (s : Bool) :
    face d k i s ≃ Cube d k where
  toFun x := i.removeNth x.1
  invFun y := ⟨i.insertNth (endpoint k s) y, Fin.insertNth_apply_same ..⟩
  left_inv x := Subtype.ext (Fin.insertNth_eq_iff.mpr ⟨x.2.symm, rfl⟩)
  right_inv _ := Fin.removeNth_insertNth ..

theorem crossingCount (d k : ℕ) :
    ∑ i : Fin (d+1), ∑ s : Bool, (Fintype.card (face d k i s) : ℝ) =
      (2*((d+1:ℕ):ℝ)) * area (d+1) k := by
  simp_rw [fun i s => Fintype.card_congr (faceEquiv d k i s)]
  simp [Cube, area]
  ring

/-- Sum the original lattice conductances of all edges identified by shorting. -/
noncomputable def cutConductance (d k : ℕ) (p : ℝ) : ℝ :=
  ∑ i : Fin (d+1), ∑ s : Bool, ∑ _x : face d k i s, p^(k+1) / (2*((d+1:ℕ):ℝ))

theorem cutConductance_eq (d k : ℕ) (p : ℝ) :
    cutConductance d k p = conductance (d+1) k p := by
  have hc := crossingCount d k
  unfold cutConductance
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp_rw [← Finset.sum_mul]
  rw [hc]
  unfold conductance
  field_simp

end Metropolis.Shell
