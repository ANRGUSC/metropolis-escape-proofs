import Metropolis.FlowDirichletStatement
import Metropolis.FlowThomson
import Metropolis.FlowPyramid

namespace Metropolis.Flow

theorem face_resistance_upper : FaceResistanceStatement := by
  intro D hD p hp hp'
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : D ≠ 0)
  obtain ⟨C,hC,h⟩ := face_flow_bound n hp hp'
  refine ⟨C,hC,?_⟩
  intro N hN
  obtain ⟨b,hb,he⟩ := h N hN
  exact (weak_thomson hp _ b hb).trans (ENNReal.ofReal_le_ofReal (by simpa [one_div] using he))

end Metropolis.Flow
