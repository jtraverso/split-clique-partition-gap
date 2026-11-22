module

public import SplitGap

public section

namespace GapExtremal.R434
open Real

/-- For every sufficiently large order, a connected split graph retains connectivity after deletion of fewer than ceiling(n/5) vertices and has the displayed lower bound for cp(G) minus cp*(G). -/
theorem nearly_quadratic_gap_with_linear_connectivity :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
        Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧
        SurvivesCuts G ((n+4)/5) ∧
        2 * orderAmplitude 78375 (200*(1080/7)^2) (log (24/7)) * n^2 /
          (log n)^(5/2 : ℝ) * exp (-2 * sqrt (log (24/7) * log n)) ≤ gap G := universal_R434_linear

/-- The bound also holds when the fractional partition is restricted to cliques of order at most four. The integral cost is unrestricted. -/
theorem nearly_quadratic_gap_with_fractional_pieces_at_most_four :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V),
        Fintype.card V = n ∧ IsSplit G ∧ G.Connected ∧
        SurvivesCuts G ((n+4)/5) ∧
        2 * orderAmplitude 78375 (200*(1080/7)^2) (log (24/7)) * n^2 /
          (log n)^(5/2 : ℝ) * exp (-2 * sqrt (log (24/7) * log n)) ≤ gapWithFracFour G := universal_R434_linear_mixed

end GapExtremal.R434
