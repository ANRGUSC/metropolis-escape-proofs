import Metropolis.ShellQuotientRelease
import Metropolis.ShellQuotientCompleteContract

namespace Metropolis.Shell

theorem actualLink_eq (d N k : ℕ) (hk : k < N) (p : ℝ) :
    actualLink d N k p = shortedLink d N k hk p := by
  classical
  let weight := fun q : Crossing d N k => p^height q.1.1 * latticeRow p q.1.1 q.1.2
  calc actualLink d N k p =
      ∑ e : Outward d k, weight (crossingEquiv d N k hk e) :=
        ((crossingEquiv d N k hk).sum_comp weight).symm
    _ = shortedLink d N k hk p := by
        unfold shortedLink
        rw [Fintype.sum_sigma]
        apply Finset.sum_congr rfl
        intro i _
        rw [Fintype.sum_sigma]
        rfl

theorem paper_quotient_complete : FullQuotientStatement := by
  intro d N p hp hp1
  obtain ⟨balance,rows,origin⟩ := paper_quotient d N p hp hp1
  refine ⟨balance, fun k hk => ⟨crossMap_injective hk, crossMap_surjective hk⟩, ?_, ?_⟩
  · intro k hk
    rw [actualLink_eq d N (k+1) hk, actualLink_eq d N k (by omega)]
    exact rows k hk
  · intro hn
    rw [actualLink_eq d N 0 hn]
    exact origin hn

#print axioms paper_quotient_complete
end Metropolis.Shell
