import Metropolis.FlowScaling
import Metropolis.Mass
import Metropolis.Hitting
import Metropolis.LowerPaper

namespace Metropolis.Flow

theorem true_chain_scaling : TrueScalingStatement :=
  true_scaling_of_hitting_bounds Lower.escape_lower
    (fun _ _ _ hp hp' => Lattice.total_mass_ne_top hp hp')
    (fun _ _ hD hp hp' _ hFin hA ha => Lattice.meanHitting_le_mass_resistance hD hp hp' hA hFin ha)

end Metropolis.Flow
