module

public import SplitGapIII.RecoveryProbability
public import SplitGapIV.QuantitativeRecovery

@[expose] public section

namespace SplitGapIIIRegistry
open Finset MeasureTheory ProbabilityTheory GapExtremal Filter
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
  rw [SplitGapIII.gap_of_complete_recovery B N independent initial hinitial]
  exact SplitGapIII.probability_gap_deviation B N independent keep hkeep hcoin p hp tests
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
    ∃ host : J → H, (∀ e, host e ∈ lists e) ∧ HasHostAssignment N J host := by
  obtain ⟨host, hlist, hproper⟩ :=
    SplitGapIII.recover_bipartite_from_midpoints left right midpoint midpoint_proper lists large
  refine ⟨host, hlist, fun e => physical e _ (hlist e), ?_⟩
  intro e f hh v he hf
  by_contra hne
  apply hproper e f hne _ hh
  rw [ends e, mem_insert, mem_singleton] at he
  rw [ends f, mem_insert, mem_singleton] at hf
  rcases he with he | he <;> rcases hf with hf | hf
  · exact Or.inl (he.symm.trans hf)
  · exact (sides e f (he.symm.trans hf)).elim
  · exact (sides f e (hf.symm.trans he)).elim
  · exact Or.inr (he.symm.trans hf)


/-- Vertex types for the split witness built from the two shared indices per core vertex. -/
abbrev IndexedCore (s : ℕ) := (Fin 3 × Fin 5) × Fin s × Fin s

abbrev IndexedHosts (s n : ℕ) := Fin (n - Fintype.card (IndexedCore s))

/-- The neighborhood in the graph of surviving crossing incidences. -/
noncomputable def survivingNeighborhood
    (N : H → Finset V) (keep : H × V → Set Ω) (ω : Ω) (h : H) : Finset V := by
  classical
  exact (N h).filter fun v => ω ∈ keep (h,v)

/-- An n-vertex witness with exact gap preservation and complete physical recovery
at logarithmic two-incidence supply. The neighborhoods are fixed before deletion. -/
theorem quantitative_recovery_at_logarithmic_supply
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 2 ≤ n) (hlog : 120 ≤ Real.log n)
    (p : ℝ≥0∞) (hp : p.toReal ≤ 1) (hsupply : 471859200 * Real.log n ≤ p.toReal^2 * (n : ℝ)) :
    ∃ s : ℕ, ∃ B : SimpleGraph (IndexedCore s), ∃ inst : DecidableRel B.Adj,
      let _ := inst
      ∃ N : IndexedHosts s n → Finset (IndexedCore s),
      Fintype.card (IndexedCore s ⊕ IndexedHosts s n) = n ∧
      (∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b) ∧
      2/9 * (s : ℝ)^3 ≤ gap (hostGraph N) ∧
      (4/81 : ℝ) * (p.toReal * (n : ℝ) / 56623104000)^3 ≤ (gap (hostGraph N))^2 ∧
      ∀ keep : IndexedHosts s n × IndexedCore s → Set Ω,
        (∀ r, MeasurableSet (keep r)) → iIndepSet keep μ → (∀ r, μ (keep r) = p) →
        μ.real {ω | ¬ ((∃ host : jPairs B univ → IndexedHosts s n,
          HasHostAssignment (survivingNeighborhood N keep ω) (jPairs B univ) host) ∧
          gap (hostGraph (survivingNeighborhood N keep ω)) = gap (hostGraph N))} ≤
          2 * Real.exp (-8 * Real.log n) := by
  obtain ⟨s,N,hcard,hind,hgap,hscale,hrec⟩ :=
    SplitGapIV.indexed_quantitative_physical_recovery μ n hn hlog p hp hsupply
  exact ⟨s,SplitGapIV.indexedResidual (Fin s),inferInstance,N,hcard,hind,hgap,hscale,hrec⟩

end SplitGapIIIRegistry
