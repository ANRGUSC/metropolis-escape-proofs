import Std

namespace Metropolis

-- L is the inner interval's size. Vertex 0 is the leftmost new vertex.
-- Scale all rational masses and currents by L(L+2), a positive integer.
def current (L t : Int) : Int :=
  if 0 ≤ t ∧ t ≤ L then 2*t - L else 0

def innerMass (L t : Int) : Int :=
  if 1 ≤ t ∧ t ≤ L then L+2 else 0

def outerMass (L t : Int) : Int :=
  if 0 ≤ t ∧ t ≤ L+1 then L else 0

theorem balance (L t : Int) (h : 0 < L) :
    current L t - current L (t-1) = innerMass L t - outerMass L t := by
  unfold current innerMass outerMass
  split <;> split <;> split <;> split <;> omega

def energy (L : Int) : Nat → Int
  | 0 => 0
  | n+1 => energy L n + current L n * current L n

theorem edge_bound (L t : Int) (h : 0 < L) :
    current L t * current L t ≤ L*L := by
  have bounds : -L ≤ current L t ∧ current L t ≤ L := by
    unfold current
    split <;> omega
  have prod := Int.mul_nonneg (show 0 ≤ L - current L t by omega)
    (show 0 ≤ L + current L t by omega)
  grind

theorem energy_bound (L : Int) (h : 0 < L) (n : Nat) :
    energy L n ≤ (n : Int) * (L*L) := by
  induction n with
  | zero => simp [energy]
  | succ n ih =>
    have := edge_bound L n h
    simp only [energy, Int.natCast_succ, Int.add_mul, Int.one_mul]
    omega

-- This is the paper's 1D energy inequality multiplied by (k+1)[L(L+2)]².
theorem transport_one_dimension (k : Nat) :
    let L : Int := 2*(k : Int)+1
    (∀ t : Int, current L t - current L (t-1) = innerMass L t - outerMass L t) ∧
    ((k : Int)+1) * energy L (2*k+2) ≤ (L*(L+2))*(L*(L+2)) := by
  dsimp only
  let L : Int := 2*(k : Int)+1
  have hL : 0 < L := by dsimp [L]; omega
  constructor
  · exact fun t => balance L t hL
  · have h := energy_bound L hL (2*k+2)
    have step := Int.mul_le_mul_of_nonneg_left h (show 0 ≤ (k : Int)+1 by omega)
    have count : ((2*k+2 : Nat) : Int) = L+1 := by dsimp [L]; omega
    rw [count] at step
    have scale : ((k : Int)+1)*(L+1) ≤ (L+2)*(L+2) := by
      apply Int.mul_le_mul <;> dsimp [L] <;> omega
    have finish := Int.mul_le_mul_of_nonneg_right scale
      (Int.mul_nonneg (Int.le_of_lt hL) (Int.le_of_lt hL))
    change ((k : Int)+1)*energy L (2*k+2) ≤ (L*(L+2))*(L*(L+2))
    grind

-- Check the type against an independently spelled-out denominator-cleared contract.
example (k : Nat) :
    let w : Int := 2*(k : Int)+1
    (∀ i : Int, current w i - current w (i-1) = innerMass w i - outerMass w i) ∧
    ((k : Int)+1)*energy w (2*k+2) ≤ (w*(w+2))*(w*(w+2)) :=
  transport_one_dimension k

#print axioms transport_one_dimension
end Metropolis
