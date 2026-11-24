module

public import SplitGapIII.RecoveryProbability

@[expose] public section

namespace SplitGapIIIRegistry
open Finset MeasureTheory ProbabilityTheory GapExtremal SplitGapIII Filter
open scoped BigOperators ENNReal Topology

/-- A proper host assignment uses present crossing edges and never reuses one. -/
def HasHostAssignment {V H : Type*} (N : H → Finset V)
    (J : Finset (Finset V)) (host : J → H) : Prop :=
  (∀ e, e.val ⊆ N (host e)) ∧
  ∀ e f, host e = host f → ∀ v ∈ e.val, v ∈ f.val → e = f

/-- A host survives for a request when both of its crossing incidences survive. -/
noncomputable def survivingHosts {Ω V H : Type*} (available : Finset H)
    (keep : H × V → Set Ω) (a b : V) (ω : Ω) : Finset H := by
  classical
  exact available.filter fun h => ω ∈ keep (h, a) ∧ ω ∈ keep (h, b)

variable {Ω E V H : Type*}

/-- When a complete assignment exists before deletion, sufficient surviving lists
bound the probability that the original gap changes. The rule that turns these
lists into an assignment is an explicit hypothesis. -/
theorem failure_probability_after_crossing_deletions
    [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : SimpleGraph V) [DecidableRel B.Adj] (N : H → Finset V)
    (independent : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (initial : jPairs B univ → H) (hinitial : HasHostAssignment N (jPairs B univ) initial)
    (keep : H × V → Set Ω) (hkeep : ∀ r, MeasurableSet (keep r))
    (hcoin : iIndepSet keep μ) (p : ℝ≥0∞) (hp : ∀ r, μ (keep r) = p)
    (tests : Finset E) (left right : E → V) (distinct : ∀ e, left e ≠ right e)
    (available : E → Finset H) (a t : ℝ) (ht : t ≤ 0)
    (live : Ω → H → Finset V)
    (hlive : ∀ ω h v, v ∈ live ω h ↔ v ∈ N h ∧ ω ∈ keep (h, v))
    (recover : ∀ ω, (∀ e ∈ tests, a * (available e).card <
      (survivingHosts (available e) keep (left e) (right e) ω).card) →
      ∃ host : jPairs B univ → H, HasHostAssignment (live ω) (jPairs B univ) host) :
    μ.real {ω | gap (hostGraph (live ω)) ≠ gap (hostGraph N)} ≤
      ∑ e ∈ tests, (Real.exp (-t * a) * (1 - p.toReal ^ 2 + p.toReal ^ 2 * Real.exp t)) ^
        (available e).card := by
  rw [gap_of_complete_recovery B N independent initial hinitial]
  exact probability_gap_deviation B N independent keep hkeep hcoin p hp tests
    left right distinct available a t ht live hlive recover

/-- A proper bipartite midpoint labeling gives a surviving host assignment
whenever each physical list has at least the number of available labels. -/
theorem recover_bipartite_physical_lists
    [Fintype V] [DecidableEq V]
    {S : Type*} [Fintype S] (N : H → Finset V) (J : Finset (Finset V))
    (left right : J → V) (midpoint : J → S)
    (ends : ∀ e, e.val = {left e, right e})
    (sides : ∀ e f, left e ≠ right f)
    (midpoint_proper : ∀ e f, e ≠ f → (left e = left f ∨ right e = right f) →
      midpoint e ≠ midpoint f)
    (lists : J → Finset H)
    (physical : ∀ e h, h ∈ lists e → e.val ⊆ N h)
    (large : ∀ e, Fintype.card S ≤ (lists e).card) :
    ∃ host : J → H, HasHostAssignment N J host := by
  exact recover_physical_bipartite_group N J left right midpoint ends sides midpoint_proper
    lists physical large

end SplitGapIIIRegistry
