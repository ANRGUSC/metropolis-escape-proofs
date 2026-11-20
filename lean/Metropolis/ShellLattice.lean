import Metropolis.ShellQuotient

namespace Metropolis.Shell

/-- Embed a point of the inner cube into the fixed reflecting box B_N. -/
def embedCube {D k N : ℕ} (hk : k ≤ N) (x : Cube D k) : Cube D N :=
  fun j => ⟨(x j).val + (N-k), by have := (x j).isLt; omega⟩

/-- Target of a signed outward step at coordinate i. -/
def outerNeighbor {D k N : ℕ} (hk : k < N) (x : Cube D k)
    (i : Fin D) (s : Bool) : Cube D N := fun j =>
  if j = i then
    if s then ⟨N+k+1, by omega⟩ else ⟨N-(k+1), by omega⟩
  else embedCube hk.le x j

private theorem embedded_le {D k N : ℕ} (hk : k ≤ N) (x : Cube D k) (j : Fin D) :
    max ((embedCube hk x j).val - N) (N - (embedCube hk x j).val) ≤ k := by
  have := (x j).isLt
  simp only [embedCube, max_le_iff]; omega

theorem height_face {D k N : ℕ} (hk : k ≤ N) (x : Cube D k) (i : Fin D)
    (s : Bool) (hx : x i = endpoint k s) : height (embedCube hk x) = k := by
  apply le_antisymm
  · exact Finset.sup_le fun j _ => embedded_le hk x j
  · have h : max ((embedCube hk x i).val - N) (N - (embedCube hk x i).val) ≤
        height (embedCube hk x) := Finset.le_sup (f := fun j => max ((embedCube hk x j).val-N) (N-(embedCube hk x j).val)) (Finset.mem_univ i)
    cases s with
    | false =>
      have hxi : (x i).val = 0 := congrArg Fin.val hx
      simp [embedCube, hxi] at h
      omega
    | true =>
      have hxi : (x i).val = 2*k := congrArg Fin.val hx
      simp [embedCube, hxi] at h
      omega

theorem height_outer {D k N : ℕ} (hk : k < N) (x : Cube D k) (i : Fin D)
    (s : Bool) : height (outerNeighbor hk x i s) = k+1 := by
  apply le_antisymm
  · apply Finset.sup_le
    intro j _
    by_cases hj : j = i
    · subst j; cases s <;> simp [outerNeighbor] <;> omega
    · simpa [outerNeighbor, hj] using (embedded_le hk.le x j).trans (Nat.le_succ k)
  · have h : max ((outerNeighbor hk x i s i).val - N) (N - (outerNeighbor hk x i s i).val) ≤
        height (outerNeighbor hk x i s) := Finset.le_sup (f := fun j => max ((outerNeighbor hk x i s j).val-N) (N-(outerNeighbor hk x i s j).val)) (Finset.mem_univ i)
    cases s <;> simp [outerNeighbor] at h <;> omega

theorem adjacent_face {D k N : ℕ} (hk : k < N) (x : Cube D k) (i : Fin D)
    (s : Bool) (hx : x i = endpoint k s) :
    adjacent (embedCube hk.le x) (outerNeighbor hk x i s) := by
  refine ⟨i, ?_, fun j hj => by simp [outerNeighbor, hj]⟩
  cases s with
  | false =>
    have hxi : (x i).val = 0 := congrArg Fin.val hx
    right
    simp [embedCube, outerNeighbor, hxi]
    omega
  | true =>
    have hxi : (x i).val = 2*k := congrArg Fin.val hx
    left
    simp [embedCube, outerNeighbor, hxi]
    omega

/-- At every transient shell, each edge represented by a face actually has
the weight used in the quotient sum, even when it lands on the reflecting boundary. -/
theorem outward_edge_weight {D k N : ℕ} (hk : k < N) (x : Cube D k) (i : Fin D)
    (s : Bool) (hx : x i = endpoint k s) (p : ℝ) :
    p ^ height (embedCube hk.le x) * latticeRow p (embedCube hk.le x) (outerNeighbor hk x i s)
      = p^(k+1)/(2*(D:ℝ)) := by
  have he := height_face hk.le x i s hx
  have ho := height_outer hk x i s
  have hne : embedCube hk.le x ≠ outerNeighbor hk x i s := by
    intro h
    rw [h, ho] at he; omega
  simp [latticeRow, accepted, hne, adjacent_face hk x i s hx, he, ho, pow_succ, mul_div_assoc]

/-- A shell site represented as a point of its enclosing unshifted cube. -/
def sitePoint {D : ℕ} (k : ℕ) : ShellSites D k → Cube D k := by
  cases k with
  | zero => exact id
  | succ k => exact Subtype.val

theorem sitePoint_height (d k N : ℕ) (hk : k ≤ N) (x : ShellSites (d+1) k) :
    height (embedCube hk (sitePoint k x)) = k := by
  classical
  cases k with
  | zero =>
    apply height_face hk _ (0 : Fin (d+1)) false
    apply Fin.ext
    have h := ((sitePoint 0 x) (0 : Fin (d+1))).isLt
    change ((sitePoint 0 x) (0 : Fin (d+1))).val = 0
    omega
  | succ k =>
    have hx := x.2
    change ¬∀ i, 0 < (x.1 i).val ∧ (x.1 i).val + 1 < 2*(k+1)+1 at hx
    obtain ⟨i,hi⟩ := Classical.not_forall.mp hx
    have hlt := (x.1 i).isLt
    change height (embedCube hk x.1) = k+1
    by_cases h : (x.1 i).val = 0
    · apply height_face hk _ i false
      apply Fin.ext; simpa [endpoint] using h
    · apply height_face hk _ i true
      apply Fin.ext; simp [endpoint]; omega

end Metropolis.Shell
