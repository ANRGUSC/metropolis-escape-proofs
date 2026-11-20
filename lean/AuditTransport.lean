import Metropolis.TransportProduct

/-- The uniform mass on the inner cube is extended by zero at the outer boundary.
Each positive-axis edge is counted once. -/
def TransportPaperStatement : Prop :=
  ∀ n k : ℕ, 1 ≤ n →
    ∃ J : Metropolis.Cube.Edge k n → ℝ,
      (∀ x, Metropolis.Cube.div k n J x =
        Metropolis.Cube.tensor k (Metropolis.Cube.inner k) n x -
        Metropolis.Cube.tensor k (Metropolis.Cube.outer k) n x) ∧
      Metropolis.Cube.edgeSum k n (fun e => J e ^ 2) ≤ (n : ℝ) / ((k : ℝ) + 1) ^ n
