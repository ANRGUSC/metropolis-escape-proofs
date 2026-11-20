import Metropolis.LowerMean
import Metropolis.LowerFlux

namespace Metropolis.Lower

/-- Theorem 3 for the original walk on the integer lattice. -/
theorem escape_lower : EscapeLowerStatement := by
  apply lower_from_cut_flux
  intro d k p hp hp'
  exact (stationaryExit_le_dirichlet (D:=d+1) k hp).trans (dirichlet_cubeTest d k hp hp'.le)

end Metropolis.Lower
