import Transport
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! One axis of the cube, enumerated from the left exterior vertex to the right.
The positive direction is toward the next index. -/
noncomputable section

namespace Metropolis.Cube

abbrev Axis (k : ℕ) := Fin (2*k+3)
abbrev Link (k : ℕ) := Fin (2*k+2)

def inner (k : ℕ) (x : Axis k) : ℝ :=
  if x.val = 0 ∨ x.val = 2*k+2 then 0 else (2*(k:ℝ)+1)⁻¹

def outer (k : ℕ) (_ : Axis k) : ℝ := (2*(k:ℝ)+3)⁻¹

def lineFlow (k : ℕ) (i : Link k) : ℝ :=
  (Metropolis.current (2*(k:ℤ)+1) (i.val:ℤ) : ℝ) / ((2*(k:ℝ)+1)*(2*(k:ℝ)+3))

def lineDiv (k : ℕ) (f : Link k → ℝ) (x : Axis k) : ℝ :=
  (if h : x.val < 2*k+2 then f ⟨x.val,h⟩ else 0) -
    (if h : x.val = 0 then 0 else f ⟨x.val-1,by have := x.isLt; omega⟩)

theorem lineDiv_mul (k : ℕ) (f : Link k → ℝ) (a : ℝ) (x : Axis k) :
    lineDiv k (fun i => f i * a) x = lineDiv k f x * a := by
  unfold lineDiv
  split <;> split <;> ring

theorem line_balance (k : ℕ) (x : Axis k) :
    lineDiv k (lineFlow k) x = inner k x - outer k x := by
  have hx := x.isLt
  have h := Metropolis.balance (2*(k:ℤ)+1) x.val (by omega)
  have hbig : (0:ℝ) < 2*k+3 := by positivity
  have hsmall : (0:ℝ) < 2*k+1 := by positivity
  let den : ℝ := (2*(k:ℝ)+1)*(2*(k:ℝ)+3)
  have hout : (if h : x.val < 2*k+2 then lineFlow k ⟨x.val,h⟩ else 0) =
      (Metropolis.current (2*(k:ℤ)+1) x.val : ℝ) / den := by
    split
    · rfl
    · simp [Metropolis.current, show ¬ (x.val:ℤ) ≤ 2*(k:ℤ)+1 by omega]
  have hin : (if h : x.val = 0 then (0:ℝ) else lineFlow k ⟨x.val-1,by omega⟩) =
      (Metropolis.current (2*(k:ℤ)+1) ((x.val:ℤ)-1) : ℝ) / den := by
    split
    · rename_i he; simp [he,Metropolis.current]
    · simp [lineFlow,den,Nat.cast_sub (show 1 ≤ x.val by omega)]
  rw [lineDiv,hout,hin,← sub_div,← Int.cast_sub,h]
  unfold Metropolis.innerMass Metropolis.outerMass
  rw [if_pos (show 0 ≤ (x.val:ℤ) ∧ (x.val:ℤ) ≤ (2*(k:ℤ)+1)+1 by omega)]
  unfold inner outer
  split <;> split <;> try omega
  all_goals push_cast; dsimp [den]; field_simp; ring

theorem line_energy (k : ℕ) :
    ∑ i : Link k, lineFlow k i ^ 2 ≤ ((k:ℝ)+1)⁻¹ := by
  have hsmall : (0:ℝ) < 2*k+1 := by positivity
  have hbig : (0:ℝ) < 2*k+3 := by positivity
  calc
    _ ≤ ∑ _i : Link k, ((2*(k:ℝ)+3)⁻¹)^2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := Metropolis.edge_bound (2*(k:ℤ)+1) i.val (by omega)
      have hr : (Metropolis.current (2*(k:ℤ)+1) i.val : ℝ)^2 ≤ (2*(k:ℝ)+1)^2 := by
        simpa [pow_two] using (show ((Metropolis.current (2*(k:ℤ)+1) i.val * Metropolis.current (2*(k:ℤ)+1) i.val:ℤ):ℝ) ≤ (((2*(k:ℤ)+1)*(2*(k:ℤ)+1):ℤ):ℝ) by exact_mod_cast h)
      unfold lineFlow
      rw [div_pow, mul_pow, inv_pow]
      apply (div_le_iff₀ (mul_pos (pow_pos hsmall 2) (pow_pos hbig 2))).2
      calc
        _ ≤ (2*(k:ℝ)+1)^2 := hr
        _ = _ := by field_simp
    _ ≤ _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      rw [inv_pow, ← div_eq_mul_inv]
      apply (div_le_iff₀ (pow_pos hbig 2)).2
      rw [inv_mul_eq_div]
      apply (le_div_iff₀ (by positivity : (0:ℝ)<k+1)).2
      nlinarith [sq_nonneg (k:ℝ), Nat.cast_nonneg (α:=ℝ) k]

theorem outer_square (k : ℕ) :
    ∑ x : Axis k, outer k x ^ 2 ≤ ((k:ℝ)+1)⁻¹ := by
  simp [outer, inv_pow, ← div_eq_mul_inv]
  field_simp
  nlinarith [Nat.cast_nonneg (α:=ℝ) k, sq_nonneg (k:ℝ)]

theorem inner_square (k : ℕ) :
    ∑ x : Axis k, inner k x ^ 2 ≤ ((k:ℝ)+1)⁻¹ := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_castSucc]
  have hi (i : Fin (2*k+1)) : inner k i.castSucc.succ = (2*(k:ℝ)+1)⁻¹ := by
    have := i.isLt
    simp [inner, Fin.val_succ, Fin.val_castSucc, show i.val ≠ 2*k+1 by omega]
  simp only [hi]
  simp [inner, Fin.val_last, inv_pow]
  field_simp
  nlinarith [Nat.cast_nonneg (α:=ℝ) k, sq_nonneg (k:ℝ)]

end Metropolis.Cube
