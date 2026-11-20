import Metropolis.TransportCube

noncomputable section

namespace Metropolis.Cube

private theorem vertex_mul (k : ℕ) (n : ℕ) (a : ℝ) (f : Vertex k n → ℝ) :
    vertexSum k n (fun x => a * f x) = a * vertexSum k n f := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [vertexSum, ih, Finset.mul_sum]

private theorem edge_mul (k : ℕ) (n : ℕ) (a : ℝ) (f : Edge k n → ℝ) :
    edgeSum k n (fun e => a * f e) = a * edgeSum k n f := by
  induction n with
  | zero => simp [edgeSum]
  | succ n ih => simp only [edgeSum, vertex_mul, ih, mul_add, Finset.mul_sum]

private theorem div_mul (k : ℕ) (n : ℕ) (a : ℝ) (f : Edge k n → ℝ) (x : Vertex k n) :
    div k n (fun e => a * f e) x = a * div k n f x := by
  induction n with
  | zero => simp [div]
  | succ n ih =>
    obtain ⟨x,z⟩ := x
    simp only [div,ih,mul_add]
    congr 1
    simpa only [mul_comm a] using lineDiv_mul k (fun i => f (.inl (i,z))) a x

def cubeFlow (k : ℕ) : (n : ℕ) → Edge k n → ℝ
  | 0, e => nomatch e
  | n+1, .inl (i,z) => lineFlow k i * tensor k (inner k) n z
  | n+1, .inr (x,e) => outer k x * cubeFlow k n e

theorem cube_balance (k n : ℕ) (x : Vertex k n) :
    div k n (cubeFlow k n) x = tensor k (inner k) n x - tensor k (outer k) n x := by
  induction n with
  | zero => simp [div,tensor]
  | succ n ih =>
    obtain ⟨x,z⟩ := x
    simp only [div,cubeFlow,lineDiv_mul,line_balance,div_mul,ih,tensor]
    ring

private theorem vertex_nonneg (k n : ℕ) (f : Vertex k n → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ vertexSum k n f := by
  induction n with
  | zero => exact hf ()
  | succ n ih => exact Finset.sum_nonneg fun x _ => ih _ (fun z => hf (x,z))

private theorem edge_nonneg (k n : ℕ) (f : Edge k n → ℝ) (hf : ∀ e, 0 ≤ f e) :
    0 ≤ edgeSum k n f := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact add_nonneg (Finset.sum_nonneg fun i _ => vertex_nonneg k n _ (fun z => hf (.inl (i,z))))
      (Finset.sum_nonneg fun x _ => ih _ (fun e => hf (.inr (x,e))))

private theorem tensor_norm (k n : ℕ) :
    vertexSum k n (fun z => tensor k (inner k) n z ^ 2) ≤ (((k:ℝ)+1)⁻¹)^n := by
  induction n with
  | zero => simp [tensor,vertexSum]
  | succ n ih =>
    simp only [vertexSum,tensor,mul_pow,vertex_mul,← Finset.sum_mul]
    rw [pow_succ']
    exact mul_le_mul (inner_square k) ih (vertex_nonneg k n _ (fun _ => sq_nonneg _)) (by positivity)

theorem cube_energy (k n : ℕ) :
    edgeSum k n (fun e => cubeFlow k n e ^ 2) ≤ (n:ℝ) * (((k:ℝ)+1)⁻¹)^n := by
  induction n with
  | zero => simp [edgeSum]
  | succ n ih =>
    simp only [edgeSum,cubeFlow,mul_pow,vertex_mul,edge_mul,← Finset.sum_mul]
    have first := mul_le_mul (line_energy k) (tensor_norm k n)
      (vertex_nonneg k n _ (fun _ => sq_nonneg _)) (by positivity)
    have second := mul_le_mul (outer_square k) ih
      (edge_nonneg k n _ (fun _ => sq_nonneg _)) (by positivity)
    calc
      _ ≤ _ := add_le_add first second
      _ = _ := by rw [pow_succ]; push_cast; ring

theorem transport_nested_cubes : TransportStatement := by
  intro n k _
  refine ⟨cubeFlow k n, cube_balance k n, ?_⟩
  simpa [div_eq_mul_inv,inv_pow] using cube_energy k n

end Metropolis.Cube
