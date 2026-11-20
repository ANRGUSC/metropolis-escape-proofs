import Metropolis.Green

open scoped ENNReal
namespace Metropolis.Lower
open Metropolis.Green
noncomputable section
variable {S : Type*} [DecidableEq S]

def exitRow (P : Kernel S) (A : Set S) [DecidablePred (· ∈ A)] (x : S) : ℝ≥0∞ :=
  if x ∈ A then 0 else ∑' y, if y ∈ A then P x y else 0

def stationaryExit (P : Kernel S) (μ : S → ℝ≥0∞) (A : Set S) [DecidablePred (· ∈ A)] :
    ℝ≥0∞ := ∑' x, μ x * exitRow P A x

end
end Metropolis.Lower
