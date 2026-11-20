import Metropolis.ShellGeometry

namespace Metropolis.Shell

/-- Uniform proposals on the reflected cube: two sites are neighbors precisely
when a single coordinate changes by one and all others are retained. -/
def adjacent {D N : ℕ} (x y : Cube D N) : Prop :=
  ∃ i, ((x i).val + 1 = (y i).val ∨ (y i).val + 1 = (x i).val) ∧
    ∀ j, j ≠ i → x j = y j

private theorem adjacent_symm {D N : ℕ} (x y : Cube D N) : adjacent x y ↔ adjacent y x := by
  constructor <;> rintro ⟨i,hi,hj⟩ <;> exact ⟨i, hi.symm, fun j h => (hj j h).symm⟩

def height {D N : ℕ} (x : Cube D N) : ℕ :=
  Finset.univ.sup fun i => max ((x i).val-N) (N-(x i).val)

/-- The off-diagonal step probability on B_N. The code sums only over valid
neighbors, hence includes a rejected attempt to leave B_N in the holding row. -/
noncomputable def accepted {D N : ℕ} (p : ℝ) (x y : Cube D N) : ℝ := by
  classical exact if adjacent x y then p^(height y-height x)/(2*(D:ℝ)) else 0

noncomputable def latticeRow {D N : ℕ} (p : ℝ) (x y : Cube D N) : ℝ := by
  classical exact if x = y then 1-∑ z : Cube D N, accepted p x z else accepted p x y

theorem lattice_balance {D N : ℕ} (p : ℝ) (x y : Cube D N) :
    p^(height x) * latticeRow p x y = p^(height y) * latticeRow p y x := by
  classical
  by_cases hxy : x = y
  · subst y; rfl
  simp only [latticeRow, if_neg hxy, if_neg (Ne.symm hxy), accepted]
  rw [← adjacent_symm x y]
  split_ifs
  · rw [← mul_div_assoc, ← mul_div_assoc, ← pow_add, ← pow_add]
    congr 2
    omega
  · simp

/-- A signed proposal from a point of B_k crosses its outer boundary iff its
selected coordinate is on the selected face. Coordinates here are shifted into
the integer interval [0,2k], which leaves the crossing predicate unchanged. -/
theorem crosses_iff_face {D k : ℕ} (x : Cube D k) (i : Fin D) (s : Bool) :
    (let z : ℤ := (x i).val + (if s then 1 else -1);
     z < 0 ∨ (2*k:ℕ) < z) ↔ x i = endpoint k s := by
  have hx := (x i).isLt
  cases s <;> simp only [endpoint, Bool.false_eq_true, if_false,
    if_true, Fin.ext_iff, Nat.cast_mul, Nat.cast_ofNat] <;> omega

noncomputable def shellWeight (D k : ℕ) (p : ℝ) : ℝ := ∑ _ : ShellSites D k, p^k

theorem shellWeight_eq (D k : ℕ) (p : ℝ) : shellWeight D k p = mass D k p := by
  simp [shellWeight, Finset.sum_const, nsmul_eq_mul, card_shellSites, mass]

/-- Short the shell, retaining its measured occupancy; divide the sum of
crossing conductances by the vertex mass. The first two equalities give the row
at every interior shell; the third handles the origin. -/
theorem quotient_rows (d k : ℕ) {p : ℝ} (hp : 0 < p) :
    cutConductance d (k+1) p / shellWeight (d+1) (k+1) p =
        p * area (d+1) (k+1) / shellSize (d+1) (k+1) ∧
    cutConductance d k p / shellWeight (d+1) (k+1) p =
        area (d+1) k / shellSize (d+1) (k+1) ∧
    cutConductance d 0 p / shellWeight (d+1) 0 p = p := by
  simp only [cutConductance_eq, shellWeight_eq]
  exact ⟨up_eq (by omega) _ hp, by simpa [down] using down_succ (D:=d+1) (by omega) k hp,
    up_zero (d+1) p⟩

end Metropolis.Shell
