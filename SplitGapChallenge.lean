module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! Exact edge-clique partitions cover each edge once. The stronger statement
uses the fractional optimum over pieces of order at most four. Comparing that
optimum with the unrestricted integral optimum gives a lower bound for the gap
when both sides are restricted to order four. -/

@[expose] public section

open Finset
namespace SimpleGraph
variable {V : Type*}

/-- A family of cliques of order at least two containing each edge exactly once. -/
structure IsCliquePartition (G : SimpleGraph V) (P : Finset (Finset V)) : Prop where
  two_le : ∀ B ∈ P, 2 ≤ B.card
  isClique : ∀ B ∈ P, G.IsClique (B : Set V)
  existsUnique : ∀ u v, G.Adj u v → ∃! B, B ∈ P ∧ u ∈ B ∧ v ∈ B


/-- The least size of an exact clique partition. -/
noncomputable def cliquePartitionNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ P, G.IsCliquePartition P ∧ P.card = k}


variable [Fintype V]

/-- Nonnegative weights on cliques of order at least two with total weight one on every edge. -/
structure IsFracCliquePartition [DecidableEq V] (G : SimpleGraph V) (x : Finset V → ℝ) : Prop where
  nonneg : ∀ Q, 0 ≤ x Q
  support : ∀ Q, x Q ≠ 0 → 2 ≤ Q.card ∧ G.IsClique (Q : Set V)
  edge : ∀ u v, G.Adj u v → ∑ Q ∈ univ.filter (fun Q : Finset V => u ∈ Q ∧ v ∈ Q), x Q = 1


/-- The infimum of total weight over fractional clique partitions. -/
noncomputable def fracCliquePartitionNumber [DecidableEq V] (G : SimpleGraph V) : ℝ :=
  sInf {r | ∃ x, G.IsFracCliquePartition x ∧ ∑ Q, x Q = r}

end SimpleGraph

namespace GapExtremal


/-- A clique and an independent set partition the vertices. -/
def IsSplit {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ K : Set V, (∀ x ∈ K, ∀ y ∈ K, x ≠ y → G.Adj x y) ∧ (∀ x ∉ K, ∀ y ∉ K, ¬ G.Adj x y)


variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Integral partition cost minus fractional partition cost. -/
noncomputable def gap (G : SimpleGraph V) : ℝ :=
  (G.cliquePartitionNumber : ℝ) - G.fracCliquePartitionNumber


universe u_3
variable {U : Type u_3} [Fintype U] [DecidableEq U]

/-- Infimum of the total weights of fractional partitions with pieces of order at most four. -/
noncomputable def fracPartitionFour (G : SimpleGraph U) : ℝ :=
  sInf {r | ∃ x, G.IsFracCliquePartition x ∧ (∀ Q, x Q ≠ 0 → Q.card ≤ 4) ∧ ∑ Q, x Q = r}


/-- Unrestricted integral cost minus restricted fractional cost. -/
noncomputable def gapWithFracFour (G : SimpleGraph U) : ℝ :=
  (G.cliquePartitionNumber : ℝ) - fracPartitionFour G

end GapExtremal

namespace GapExtremal.R434
open Real

/-- The explicit amplitude from the order and potential estimates. -/
noncomputable def orderAmplitude (A K c : ℝ) :=
  exp (-(2 * log A + 2 + 2*c + log (27*(1+K)) - (5/2)*log c))


/-- The graph has more than k vertices and remains connected after deletion of fewer than k vertices. -/
def SurvivesCuts {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧ ∀ D : Finset V, D.card < k →
    (G.induce {v | v ∉ D}).Connected


/-- For every sufficiently large order, a connected split graph retains connectivity after deletion of fewer than ceiling(n/5) vertices and has the displayed lower bound for cp(G) minus cp*(G). -/
theorem nearly_quadratic_gap_with_linear_connectivity :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
        Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧
        SurvivesCuts G ((n+4)/5) ∧
        2 * orderAmplitude 78375 (200*(1080/7)^2) (log (24/7)) * n^2 /
          (log n)^(5/2 : ℝ) * exp (-2 * sqrt (log (24/7) * log n)) ≤ gap G := by sorry

/-- The bound also holds when the fractional partition is restricted to cliques of order at most four. The integral cost is unrestricted. -/
theorem nearly_quadratic_gap_with_fractional_pieces_at_most_four :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
        Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧
        SurvivesCuts G ((n+4)/5) ∧
        2 * orderAmplitude 78375 (200*(1080/7)^2) (log (24/7)) * n^2 /
          (log n)^(5/2 : ℝ) * exp (-2 * sqrt (log (24/7) * log n)) ≤ gapWithFracFour G := by sorry

end GapExtremal.R434
