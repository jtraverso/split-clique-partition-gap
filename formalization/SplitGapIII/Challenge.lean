module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Nat.Choose.Basic

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Recovering a clique-partition gap after crossing-edge deletions

Required pairs are the nonedges of a residual graph on a clique core.
Hosts form an independent set. A complete proper assignment puts each required pair
at a common host, with the pairs at each host forming a matching.
The probability theorem bounds failure of exact gap preservation in the same split
graph once a deterministic recovery rule is available for the stated list sizes. -/

@[expose] public section
open Finset
open scoped BigOperators

namespace SimpleGraph
variable {V : Type*}
/-- A clique partition of `G`: cliques of order at least two such that every edge of `G` lies in exactly one of
them. -/
structure IsCliquePartition (G : SimpleGraph V) (P : Finset (Finset V)) : Prop where
  two_le : ∀ B ∈ P, 2 ≤ B.card
  isClique : ∀ B ∈ P, G.IsClique (B : Set V)
  existsUnique : ∀ u v, G.Adj u v → ∃! B, B ∈ P ∧ u ∈ B ∧ v ∈ B

/-- The clique partition number `cp(G)`: the least size of a clique partition. -/
noncomputable def cliquePartitionNumber (G : SimpleGraph V) : ℕ :=
  sInf {k | ∃ P, G.IsCliquePartition P ∧ P.card = k}

variable [Fintype V]


/-- A fractional clique partition: nonnegative weights on vertex sets, supported on cliques of order at least
two, with total weight exactly one on every edge. -/
structure IsFracCliquePartition [DecidableEq V] (G : SimpleGraph V) (x : Finset V → ℝ) : Prop where
  nonneg : ∀ Q, 0 ≤ x Q
  support : ∀ Q, x Q ≠ 0 → 2 ≤ Q.card ∧ G.IsClique (Q : Set V)
  edge : ∀ u v, G.Adj u v → ∑ Q ∈ univ.filter (fun Q : Finset V => u ∈ Q ∧ v ∈ Q), x Q = 1

/-- The fractional clique partition number `cp*(G)`. -/
noncomputable def fracCliquePartitionNumber [DecidableEq V] (G : SimpleGraph V) : ℝ :=
  sInf {r | ∃ x, G.IsFracCliquePartition x ∧ ∑ Q, x Q = r}
end SimpleGraph

namespace GapExtremal
variable {V H : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

/-- The integrality gap `D G = cp G − cp* G`. -/
noncomputable def gap (G : SimpleGraph V) : ℝ :=
  (G.cliquePartitionNumber : ℝ) - G.fracCliquePartitionNumber

variable (B : SimpleGraph V) [DecidableRel B.Adj]

/-- Non-adjacent two-element subsets of `S` (the marked pairs `J` inside `S`). -/
def jPairs (S : Finset V) : Finset (Finset V) :=
  (S.powersetCard 2).filter fun p => ¬ ∃ x ∈ p, ∃ y ∈ p, B.Adj x y


/-- The split graph: core `V` (clique), hosts `H` (independent), host `h` adjacent to `N h`. -/
def hostGraph (N : H → Finset V) : SimpleGraph (V ⊕ H) where
  Adj a b :=
    match a, b with
    | .inl x, .inl y => x ≠ y
    | .inl x, .inr h => x ∈ N h
    | .inr h, .inl x => x ∈ N h
    | .inr _, .inr _ => False
  symm := ⟨fun a b h => by
    rcases a with x | h <;> rcases b with y | h' <;> simp_all [eq_comm]⟩
  loopless := ⟨fun a h => by rcases a with x | h <;> simp_all⟩

end GapExtremal

namespace SplitGapIII
open Finset
variable {Ω V H : Type*}

/-- A request is a core pair. Equal host choices at an endpoint must be the same request. -/
def Assigned (N : H → Finset V) (J : Finset (Finset V)) (host : J → H) : Prop :=
  (∀ e, e.val ⊆ N (host e)) ∧
  ∀ e f, host e = host f → ∀ v ∈ e.val, v ∈ f.val → e = f

/-- Both crossing edges of a candidate must survive. -/
noncomputable def surviving_hosts (available : Finset H) (keep : H × V → Set Ω)
    (a b : V) (ω : Ω) : Finset H := by
  classical
  exact available.filter fun h => ω ∈ keep (h, a) ∧ ω ∈ keep (h, b)

end SplitGapIII
namespace SplitGapIIIRegistry
open Finset MeasureTheory ProbabilityTheory GapExtremal SplitGapIII Filter
open scoped BigOperators ENNReal Topology

variable {Ω E V H : Type*}

/-- When a complete assignment exists before deletion, sufficient surviving lists
bound the probability that the original gap changes. The rule that turns these
lists into an assignment is an explicit hypothesis. -/
theorem failure_probability_after_crossing_deletions
    [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : SimpleGraph V) [DecidableRel B.Adj] (N : H → Finset V)
    (independent : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (initial : jPairs B univ → H) (hinitial : Assigned N (jPairs B univ) initial)
    (keep : H × V → Set Ω) (hkeep : ∀ r, MeasurableSet (keep r))
    (hcoin : iIndepSet keep μ) (p : ℝ≥0∞) (hp : ∀ r, μ (keep r) = p)
    (tests : Finset E) (left right : E → V) (distinct : ∀ e, left e ≠ right e)
    (available : E → Finset H) (a t : ℝ) (ht : t ≤ 0)
    (live : Ω → H → Finset V)
    (hlive : ∀ ω h v, v ∈ live ω h ↔ v ∈ N h ∧ ω ∈ keep (h, v))
    (recover : ∀ ω, (∀ e ∈ tests, a * (available e).card <
      (surviving_hosts (available e) keep (left e) (right e) ω).card) →
      ∃ host : jPairs B univ → H, Assigned (live ω) (jPairs B univ) host) :
    μ.real {ω | gap (hostGraph (live ω)) ≠ gap (hostGraph N)} ≤
      ∑ e ∈ tests, (Real.exp (-t * a) * (1 - p.toReal ^ 2 + p.toReal ^ 2 * Real.exp t)) ^
        (available e).card := by
  sorry

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
    ∃ host : J → H, Assigned N J host := by
  sorry

end SplitGapIIIRegistry
