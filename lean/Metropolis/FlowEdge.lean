import Metropolis.FlowBox

noncomputable section
namespace Metropolis.Flow
open Metropolis.Lattice Cube

/-- Tail and head in the finite positive-coordinate edge enumeration. -/
def edgeFrom (k : ℕ) : (n : ℕ) → Edge k n → Vertex k n
  | 0, e => nomatch e
  | n+1, .inl (i,z) => (i.castSucc,z)
  | n+1, .inr (x,e) => (x,edgeFrom k n e)

def edgeTo (k : ℕ) : (n : ℕ) → Edge k n → Vertex k n
  | 0, e => nomatch e
  | n+1, .inl (i,z) => (i.succ,z)
  | n+1, .inr (x,e) => (x,edgeTo k n e)

def direction (k : ℕ) : (n : ℕ) → Edge k n → Fin n
  | 0, e => nomatch e
  | n+1, .inl _ => 0
  | n+1, .inr (_,e) => (direction k n e).succ

theorem edge_endpoint (k n : ℕ) (e : Edge k n) :
    step (cubeCoords k n (edgeFrom k n e)) (direction k n e) 1 =
      cubeCoords k n (edgeTo k n e) := by
  induction n with
  | zero => exact Empty.elim e
  | succ n ih =>
    change (Link k × Vertex k n) ⊕ (Axis k × Edge k n) at e
    rcases e with ⟨i,z⟩ | ⟨x,e⟩
    · simp only [cubeCoords,edgeFrom,edgeTo,direction,step_first,Fin.val_castSucc,Fin.val_succ]
      congr 1
      push_cast
      ring
    · simp only [cubeCoords,edgeFrom,edgeTo,direction,step_tail,ih]

theorem edge_index_injective (k n : ℕ) :
    Function.Injective (fun e : Edge k n => (edgeFrom k n e, direction k n e)) := by
  induction n with
  | zero => intro e; exact Empty.elim e
  | succ n ih =>
    intro e d h
    change (Link k × Vertex k n) ⊕ (Axis k × Edge k n) at e d
    rcases e with ⟨i,z⟩ | ⟨x,e⟩ <;> rcases d with ⟨j,w⟩ | ⟨y,d⟩
    · obtain ⟨hpos,hdir⟩ := Prod.mk.inj h
      have hp : i.castSucc = j.castSucc ∧ z = w := Prod.mk.inj hpos
      have hij : i = j := Fin.castSucc_inj.mp hp.1
      exact congrArg Sum.inl (Prod.ext hij hp.2)
    · exact False.elim (Fin.succ_ne_zero _ (Prod.mk.inj h).2.symm)
    · exact False.elim (Fin.succ_ne_zero _ (Prod.mk.inj h).2)
    · obtain ⟨hpos,hdir⟩ := Prod.mk.inj h
      have hp : x=y ∧ edgeFrom k n e = edgeFrom k n d := Prod.mk.inj hpos
      exact congrArg Sum.inr (Prod.ext hp.1 (ih (Prod.ext hp.2 (Fin.succ_inj.mp hdir))))

theorem vertex_sum (k n : ℕ) (f : Vertex k n → ℝ) :
    vertexSum k n f = ∑ x, f x := by
  induction n with
  | zero => change f () = ∑ x : Unit, f x; exact (Fintype.sum_unique _).symm
  | succ n ih =>
    change (∑ x : Axis k, vertexSum k n (fun z => f (x,z))) =
      ∑ v : Axis k × Vertex k n, f v
    simp only [ih]
    exact (Fintype.sum_prod_type (fun z : Axis k × Vertex k n => f z)).symm

theorem edge_sum (k n : ℕ) (f : Edge k n → ℝ) : edgeSum k n f = ∑ e, f e := by
  induction n with
  | zero => change 0 = ∑ e : Empty, f e; exact (Finset.sum_empty).symm
  | succ n ih =>
    change _ = ∑ e : (Link k × Vertex k n) ⊕ (Axis k × Edge k n), f e
    simp only [edgeSum,vertex_sum,ih]
    symm
    calc _ = _ := Fintype.sum_sum_type _
         _ = _ := congrArg₂ (· + ·) (Fintype.sum_prod_type _) (Fintype.sum_prod_type _)

theorem line_parts (k : ℕ) (J : Link k → ℝ) (g : Axis k → ℝ) :
    (∑ x, lineDiv k J x * g x) = ∑ i, J i * (g i.castSucc - g i.succ) := by
  simp only [lineDiv,sub_mul,Finset.sum_sub_distrib,mul_sub]
  congr 1
  · rw [Fin.sum_univ_castSucc]
    simp [Fin.val_castSucc,Fin.val_last]
  · rw [Fin.sum_univ_succ]
    simp [Fin.val_succ]

theorem cube_parts (k n : ℕ) (J : Edge k n → ℝ) (g : Vertex k n → ℝ) :
    (∑ z, div k n J z * g z) =
      ∑ e, J e * (g (edgeFrom k n e) - g (edgeTo k n e)) := by
  induction n with
  | zero =>
    simp only [div,zero_mul,Finset.sum_const_zero]
    exact (Finset.sum_empty).symm
  | succ n ih =>
    change (∑ z : Axis k × Vertex k n, _) =
      ∑ e : (Link k × Vertex k n) ⊕ (Axis k × Edge k n), _
    simp only [Fintype.sum_prod_type,Fintype.sum_sum_type,div,edgeFrom,edgeTo,add_mul,
      Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_comm]
      simp_rw [line_parts]
      exact Finset.sum_comm
    · exact Finset.sum_congr rfl fun x _ => ih _ _

end Metropolis.Flow
