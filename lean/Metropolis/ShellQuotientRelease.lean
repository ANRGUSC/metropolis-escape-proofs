import Metropolis.ShellQuotientContract

namespace Metropolis.Shell

theorem shortedLink_eq (d N k : ℕ) (hk : k < N) (p : ℝ) :
    shortedLink d N k hk p = cutConductance d k p := by
  unfold shortedLink cutConductance
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro x _
  exact outward_edge_weight hk x.1 i s x.2 p

theorem shortedMass_eq (d N k : ℕ) (hk : k ≤ N) (p : ℝ) :
    shortedMass d N k hk p = shellWeight (d+1) k p := by
  unfold shortedMass shellWeight
  apply Finset.sum_congr rfl
  intro x _
  rw [sitePoint_height]

theorem paper_quotient : QuotientStatement := by
  intro d N p hp _
  refine ⟨lattice_balance p, ?_, ?_⟩
  · intro k hk
    simp only [shortedLink_eq, shortedMass_eq]
    exact ⟨(quotient_rows d k hp).1, (quotient_rows d k hp).2.1⟩
  · intro hn
    rw [shortedLink_eq, shortedMass_eq]
    exact (quotient_rows d 0 hp).2.2

#print axioms paper_quotient
end Metropolis.Shell
