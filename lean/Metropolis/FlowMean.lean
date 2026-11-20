import Metropolis.FlowEdge
noncomputable section
namespace Metropolis.Flow
open Metropolis.Lattice Cube

/-- Integration against the uniform law on the translated integer box. -/
def mean (r : ℕ) : (n : ℕ) → (Site n → ℝ) → ℝ
  | 0, g => g 0
  | n+1, g => ∑ i : Fin (2*r+1), (2*(r:ℝ)+1)⁻¹ *
      mean r n (fun z => g (Fin.cons ((i.val:ℤ)-r) z))

theorem box_mean (r n : ℕ) (g : Site n → ℝ) :
    (∑ z : Box r n, ((2*(r:ℝ)+1)⁻¹)^n * g (coords r n z)) = mean r n g := by
  induction n with
  | zero =>
    change (∑ _ : Unit, ((2*(r:ℝ)+1)⁻¹)^0 * g 0) = g 0
    calc _ = _ := Fintype.sum_unique _
         _ = _ := by simp
  | succ n ih =>
    change (∑ z : Fin (2*r+1) × Box r n, _) = _
    rw [Fintype.sum_prod_type (fun z : Fin (2*r+1) × Box r n => ((2*(r:ℝ)+1)⁻¹)^(n+1) * g (coords r (n+1) z))]
    simp only [mean,coords,pow_succ',mul_assoc]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.mul_sum]
    exact congrArg (fun a => (2*(r:ℝ)+1)⁻¹*a) (ih (fun z => g (Fin.cons ((i.val:ℤ)-r) z)))

theorem inner_axis_sum (k : ℕ) (f : ℤ → ℝ) :
    (∑ x : Axis k, inner k x * f ((x.val:ℤ)-(k+1))) =
      ∑ i : Fin (2*k+1), (2*(k:ℝ)+1)⁻¹ * f ((i.val:ℤ)-k) := by
  rw [Fin.sum_univ_succ,Fin.sum_univ_castSucc]
  have hi (i : Fin (2*k+1)) : inner k i.castSucc.succ = (2*(k:ℝ)+1)⁻¹ := by
    have := i.isLt
    simp [inner,show i.val ≠ 2*k+1 by omega]
  have hx (i : Fin (2*k+1)) :
      ((i.castSucc.succ.val:ℕ):ℤ)-((k:ℤ)+1) = i.val-k := by simp
  simp only [hi,hx]
  simp [inner]

theorem inner_mean (k n : ℕ) (g : Site n → ℝ) :
    (∑ z : Vertex k n, tensor k (inner k) n z * g (cubeCoords k n z)) =
      mean k n g := by
  induction n with
  | zero =>
    change (∑ _ : Unit, (1:ℝ)*g 0) = g 0
    calc _ = _ := Fintype.sum_unique _
         _ = _ := by simp
  | succ n ih =>
    change (∑ z : Axis k × Vertex k n, _) = _
    rw [Fintype.sum_prod_type (fun z : Axis k × Vertex k n => tensor k (inner k) (n+1) z * g (cubeCoords k (n+1) z))]
    simp only [tensor,cubeCoords,mul_assoc,← Finset.mul_sum]
    calc _ = ∑ x : Axis k, inner k x * mean k n (fun z => g (Fin.cons ((x.val:ℤ)-(k+1)) z)) :=
            Finset.sum_congr rfl fun x _ => congrArg (inner k x * ·) (ih _)
         _ = _ := inner_axis_sum k (fun t => mean k n (fun z => g (Fin.cons t z)))

theorem outer_mean (k n : ℕ) (g : Site n → ℝ) :
    (∑ z : Vertex k n, tensor k (outer k) n z * g (cubeCoords k n z)) =
      mean (k+1) n g := by
  induction n with
  | zero =>
    change (∑ _ : Unit, (1:ℝ)*g 0) = g 0
    calc _ = _ := Fintype.sum_unique _
         _ = _ := by simp
  | succ n ih =>
    change (∑ z : Axis k × Vertex k n, _) = _
    rw [Fintype.sum_prod_type (fun z : Axis k × Vertex k n => tensor k (outer k) (n+1) z * g (cubeCoords k (n+1) z))]
    simp only [tensor,cubeCoords,mul_assoc,← Finset.mul_sum]
    unfold mean
    apply Finset.sum_congr rfl
    intro i _
    simp only [outer,Nat.cast_add,Nat.cast_one]
    rw [show (2:ℝ)*((k:ℝ)+1)+1 = 2*k+3 by ring]
    exact congrArg ((2*(k:ℝ)+3)⁻¹ * ·) (ih (fun z => g (Fin.cons ((i.val:ℤ)-(k+1)) z)))

theorem mean_zero (n : ℕ) (g : Site n → ℝ) : mean 0 n g = g 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [mean,ih,show (Fin.cons (0:ℤ) (0 : Site n) : Site (n+1)) = 0 from
      funext (fun i => Fin.cases rfl (fun _ => rfl) i)]

end Metropolis.Flow
