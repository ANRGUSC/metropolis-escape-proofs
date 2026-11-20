import Metropolis.ShellLattice

namespace Metropolis.Shell

/-- Shorting each shell adds the original conductances of all outgoing
nearest-neighbor proposals to one link in the quotient network. -/
noncomputable def shortedLink (d N k : ℕ) (hk : k < N) (p : ℝ) : ℝ :=
  ∑ i : Fin (d+1), ∑ s : Bool, ∑ x : face d k i s,
    p ^ height (embedCube hk.le x.1) * latticeRow p (embedCube hk.le x.1) (outerNeighbor hk x.1 i s)

/-- Retain the original stationary mass of all vertices in the shell. -/
noncomputable def shortedMass (d N k : ℕ) (hk : k ≤ N) (p : ℝ) : ℝ :=
  ∑ x : ShellSites (d+1) k, p ^ height (embedCube hk (sitePoint k x))

def QuotientStatement : Prop :=
  ∀ d N : ℕ, ∀ p : ℝ, 0 < p → p ≤ 1 →
    (∀ x y : Cube (d+1) N,
      p^(height x) * latticeRow p x y = p^(height y) * latticeRow p y x) ∧
    (∀ k (hk : k+1 < N),
      shortedLink d N (k+1) hk p / shortedMass d N (k+1) hk.le p =
        p * area (d+1) (k+1) / shellSize (d+1) (k+1) ∧
      shortedLink d N k (Nat.lt_trans (Nat.lt_succ_self k) hk) p / shortedMass d N (k+1) hk.le p =
        area (d+1) k / shellSize (d+1) (k+1)) ∧
    (∀ hn : 0 < N, shortedLink d N 0 hn p / shortedMass d N 0 hn.le p = p)

end Metropolis.Shell
