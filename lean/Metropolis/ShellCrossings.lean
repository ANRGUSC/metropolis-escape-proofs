import Metropolis.ShellLattice

namespace Metropolis.Shell

abbrev Outward (d k : ℕ) := Σ i : Fin (d+1), Σ s : Bool, face d k i s
abbrev Crossing (d N k : ℕ) := {q : Cube (d+1) N × Cube (d+1) N //
  height q.1 ≤ k ∧ k < height q.2 ∧ adjacent q.1 q.2}

def crossMap {d N k : ℕ} (hk : k < N) (e : Outward d k) : Crossing d N k :=
  ⟨(embedCube hk.le e.2.2.1,outerNeighbor hk e.2.2.1 e.1 e.2.1),
    (height_face hk.le _ _ _ e.2.2.2).le, by rw [height_outer]; omega,
    adjacent_face hk _ _ _ e.2.2.2⟩

theorem embedCube_injective {D k N : ℕ} (hk : k ≤ N) : Function.Injective (@embedCube D k N hk) := by
  intro x y h
  funext j
  apply Fin.ext
  have hh := congrArg Fin.val (congrFun h j)
  simp only [embedCube] at hh
  omega

private theorem selected_changes {D k N : ℕ} (hk : k < N) (x : Cube D k) (i : Fin D)
    (s : Bool) (hf : x i = endpoint k s) :
    outerNeighbor hk x i s i ≠ embedCube hk.le x i := by
  intro h
  have hv := congrArg Fin.val h
  cases s with
  | false =>
    have hxi : (x i).val = 0 := congrArg Fin.val hf
    simp [outerNeighbor,embedCube,hxi] at hv; omega
  | true =>
    have hxi : (x i).val = 2*k := congrArg Fin.val hf
    simp [outerNeighbor,embedCube,hxi] at hv; omega

theorem crossMap_injective {d N k : ℕ} (hk : k < N) : Function.Injective (@crossMap d N k hk) := by
  rintro ⟨i,s,⟨x,hx⟩⟩ ⟨j,t,⟨y,hy⟩⟩ h
  have eq := congrArg Subtype.val h
  change (embedCube hk.le x,outerNeighbor hk x i s) = (embedCube hk.le y,outerNeighbor hk y j t) at eq
  obtain ⟨src,dst⟩ := Prod.mk.inj eq
  have hxy := embedCube_injective hk.le src
  subst y
  have hij : i=j := by
    by_contra hn
    exact selected_changes hk x i s hx ((congrFun dst i).trans (by simp [outerNeighbor,hn]))
  subst j
  have hst : s=t := by
    have hz := congrArg Fin.val (congrFun dst i)
    cases s <;> cases t <;> simp_all [outerNeighbor] <;> omega
  subst t
  rfl

private theorem coord_bounds {D N k : ℕ} (x : Cube D N) (hx : height x ≤ k) (j : Fin D) :
    N-k ≤ (x j).val ∧ (x j).val ≤ N+k := by
  have hh := (Finset.le_sup (f := fun i => max ((x i).val-N) (N-(x i).val)) (Finset.mem_univ j)).trans hx
  omega

private def unembed {D N k : ℕ} (x : Cube D N) (hx : height x ≤ k) : Cube D k := fun j =>
  ⟨(x j).val-(N-k), by have h := coord_bounds x hx j; omega⟩

private theorem embed_unembed {D N k : ℕ} (hk : k ≤ N) (x : Cube D N) (hx : height x ≤ k) :
    embedCube hk (unembed x hx) = x := by
  funext j; apply Fin.ext
  have := (coord_bounds x hx j).1
  simp only [embedCube, unembed]; omega

theorem crossMap_surjective {d N k : ℕ} (hk : k < N) : Function.Surjective (@crossMap d N k hk) := by
  rintro ⟨⟨x,y⟩,hx,hy,i,hi,ho⟩
  dsimp only at hx hy hi ho
  have hx' := coord_bounds x hx i
  have hy' : ¬(N-k ≤ (y i).val ∧ (y i).val ≤ N+k) := by
    intro h
    have hb : height y ≤ k := by
      apply Finset.sup_le
      intro j _
      by_cases hj : j=i
      · subst j; omega
      · rw [← ho j hj]; have := coord_bounds x hx j; omega
    omega
  let z := unembed x hx
  have src := embed_unembed hk.le x hx
  rcases hi with plus | minus
  · have faceZ : z i = endpoint k true := by
      apply Fin.ext
      change (x i).val-(N-k) = 2*k
      omega
    refine ⟨⟨i,true,⟨z,faceZ⟩⟩, Subtype.ext (Prod.ext src ?_)⟩
    change outerNeighbor hk z i true = y
    funext j
    by_cases hj : j=i
    · subst j; apply Fin.ext
      simp [outerNeighbor]; omega
    · exact (by simp [outerNeighbor, hj] : outerNeighbor hk z i true j = embedCube hk.le z j) |>.trans ((congrFun src j).trans (ho j hj))
  · have faceZ : z i = endpoint k false := by
      apply Fin.ext
      change (x i).val-(N-k) = 0
      omega
    refine ⟨⟨i,false,⟨z,faceZ⟩⟩, Subtype.ext (Prod.ext src ?_)⟩
    change outerNeighbor hk z i false = y
    funext j
    by_cases hj : j=i
    · subst j; apply Fin.ext
      simp [outerNeighbor]; omega
    · exact (by simp [outerNeighbor, hj] : outerNeighbor hk z i false j = embedCube hk.le z j) |>.trans ((congrFun src j).trans (ho j hj))

noncomputable def crossingEquiv (d N k : ℕ) (hk : k < N) : Outward d k ≃ Crossing d N k :=
  Equiv.ofBijective (crossMap hk) ⟨crossMap_injective hk, crossMap_surjective hk⟩

/-- The actual shorted conductance, indexed by all ordered inside-to-outside
nearest-neighbor pairs of the fixed box. -/
noncomputable def actualLink (d N k : ℕ) (p : ℝ) : ℝ := by
  classical exact ∑ q : Crossing d N k, p^height q.1.1 * latticeRow p q.1.1 q.1.2

end Metropolis.Shell
