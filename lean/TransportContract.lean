import Transport

/-- The one-dimensional transport claim, expressed in the paper's scaled units. -/
def OneDimensionalTransportClaim : Prop :=
  ∀ k : Nat,
    let innerWidth : Int := 2 * (k : Int) + 1
    let denominator := innerWidth * (innerWidth + 2)
    (∀ vertex : Int,
      Metropolis.current innerWidth vertex - Metropolis.current innerWidth (vertex - 1) =
      Metropolis.innerMass innerWidth vertex - Metropolis.outerMass innerWidth vertex) ∧
    ((k : Int) + 1) * Metropolis.energy innerWidth (2*k + 2) ≤ denominator * denominator
