import Metropolis.TransportAxis

/-! A cube is an ordered tuple of interval vertices. At positive dimension,
its edges split into axis edges at fixed tail and tail edges at fixed
first coordinate. This enumerates each unoriented nearest-neighbor edge once. -/
noncomputable section

namespace Metropolis.Cube

def Vertex (k : ℕ) : ℕ → Type
  | 0 => Unit
  | n+1 => Axis k × Vertex k n

def Edge (k : ℕ) : ℕ → Type
  | 0 => Empty
  | n+1 => (Link k × Vertex k n) ⊕ (Axis k × Edge k n)

def vertexSum (k : ℕ) : (n : ℕ) → (Vertex k n → ℝ) → ℝ
  | 0, f => f ()
  | n+1, f => ∑ x : Axis k, vertexSum k n (fun z => f (x,z))

def edgeSum (k : ℕ) : (n : ℕ) → (Edge k n → ℝ) → ℝ
  | 0, _ => 0
  | n+1, f => (∑ i : Link k, vertexSum k n (fun z => f (.inl (i,z)))) +
    ∑ x : Axis k, edgeSum k n (fun e => f (.inr (x,e)))

def div (k : ℕ) : (n : ℕ) → (Edge k n → ℝ) → Vertex k n → ℝ
  | 0, _, _ => 0
  | n+1, f, (x,z) => lineDiv k (fun i => f (.inl (i,z))) x +
    div k n (fun e => f (.inr (x,e))) z

def tensor (k : ℕ) (density : Axis k → ℝ) : (n : ℕ) → Vertex k n → ℝ
  | 0, _ => 1
  | n+1, (x,z) => density x * tensor k density n z

/-- A current with the claimed balance at every vertex and energy over all
positive-coordinate edges; index zero denotes the left exterior endpoint. -/
def TransportStatement : Prop :=
  ∀ (n k : ℕ), 1 ≤ n → ∃ f : Edge k n → ℝ,
    (∀ x, div k n f x = tensor k (inner k) n x - tensor k (outer k) n x) ∧
    edgeSum k n (fun e => f e ^ 2) ≤ (n:ℝ) / ((k:ℝ)+1)^n

end Metropolis.Cube
