module

public import SplitGapIII.Reassignment
public import SplitGapIII.RandomDeletions
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

namespace SplitGapIII
open Finset MeasureTheory ProbabilityTheory GapExtremal QuadraticExteriorPalomar Filter
open scoped BigOperators ENNReal Topology

variable {Ω E V H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

/-- Both crossing edges of a candidate must survive. -/
noncomputable def surviving_hosts (available : Finset H) (keep : H × V → Set Ω)
    (a b : V) (ω : Ω) : Finset H := by
  classical
  exact available.filter fun h => ω ∈ keep (h, a) ∧ ω ∈ keep (h, b)

theorem surviving_hosts_count (available : Finset H) (keep : H × V → Set Ω)
    (a b : V) (ω : Ω) :
    ((surviving_hosts available keep a b ω).card : ℝ) =
      ∑ h ∈ available, (⋂ r ∈ ({(h, a), (h, b)} : Finset (H × V)), keep r).indicator
        (fun _ => (1 : ℝ)) ω := by
  classical
  rw [surviving_hosts, card_eq_sum_ones, Nat.cast_sum, sum_filter]
  refine sum_congr rfl fun h _ => ?_
  have he : ω ∈ (⋂ r ∈ ({(h, a), (h, b)} : Finset (H × V)), keep r) ↔
      ω ∈ keep (h, a) ∧ ω ∈ keep (h, b) := by
    simp
  rw [Set.indicator_apply]
  split <;> simp_all

/-- The probability bound is for the original split graph after deleting its crossing incidences. -/
theorem probability_gap_deviation (B : SimpleGraph V) [DecidableRel B.Adj] (N : H → Finset V)
    (independent : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (keep : H × V → Set Ω) (hkeep : ∀ r, MeasurableSet (keep r))
    (hcoin : iIndepSet keep μ) (p : ℝ≥0∞) (hp : ∀ r, μ (keep r) = p)
    (tests : Finset E) (left right : E → V) (distinct : ∀ e, left e ≠ right e)
    (available : E → Finset H) (a t : ℝ) (ht : t ≤ 0)
    (live : Ω → H → Finset V)
    (hlive : ∀ ω h v, v ∈ live ω h ↔ v ∈ N h ∧ ω ∈ keep (h, v))
    (recover : ∀ ω, (∀ e ∈ tests, a * (available e).card <
      (surviving_hosts (available e) keep (left e) (right e) ω).card) →
      ∃ host : jPairs B univ → H, Assigned (live ω) (jPairs B univ) host) :
    μ.real {ω | gap (hostGraph (live ω)) ≠ residualSup B - residualInt B} ≤
      ∑ e ∈ tests, (Real.exp (-t * a) * (1 - p.toReal ^ 2 + p.toReal ^ 2 * Real.exp t)) ^
        (available e).card := by
  classical
  let ports (e : E) (h : H) : Finset (H × V) := {(h, left e), (h, right e)}
  have htwo (e : E) (h : H) : (ports e h).card = 2 := by
    simp [ports, distinct e]
  have hsep (e : E) (i j : H) (hne : i ≠ j) : Disjoint (ports e i) (ports e j) := by
    refine Finset.disjoint_left.mpr fun x hx hy => ?_
    have hi : x.1 = i := by simp only [ports, mem_insert, mem_singleton] at hx
                            rcases hx with hx | hx <;> simp [hx]
    have hj : x.1 = j := by simp only [ports, mem_insert, mem_singleton] at hy
                            rcases hy with hy | hy <;> simp [hy]
    exact hne (hi.symm.trans hj)
  let Good := {ω | gap (hostGraph (live ω)) = residualSup B - residualInt B}
  have hgood (ω : Ω) (hcount : ∀ e ∈ tests, a * (available e).card <
      ∑ h ∈ available e, (⋂ r ∈ ports e h, keep r).indicator (fun _ => (1 : ℝ)) ω) :
      ω ∈ Good := by
    obtain ⟨host, hhost⟩ := recover ω fun e he => by
      rw [surviving_hosts_count]
      exact hcount e he
    exact gap_of_complete_recovery B (live ω)
      (fun h v hv u hu => independent h v ((hlive ω h v).mp hv).1 u ((hlive ω h u).mp hu).1)
      host hhost
  exact physical_survival_bound tests available ports keep hkeep hcoin p hp htwo hsep a t ht Good hgood

/-- A polynomial number of tests is harmless when the smallest palette is at least sqrt(n). -/
theorem tendsto_zero_of_polynomial_tests (K : ℕ → ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hK : ∀ᶠ n in atTop, n ≤ (K n)^2) :
    Tendsto (fun n : ℕ => (n : ℝ)^2 * q ^ K n) atTop (𝓝 0) := by
  have hKinfty : Tendsto K atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [hK, eventually_ge_atTop (b^2)] with n hn hb
    by_contra h
    exact (not_le_of_gt (Nat.pow_lt_pow_left (lt_of_not_ge h) (by decide : 2 ≠ 0))) (hb.trans hn)
  have hlim := (tendsto_pow_const_mul_const_pow_of_lt_one 4 hq0 hq1).comp hKinfty
  refine squeeze_zero' (Eventually.of_forall fun _ => by positivity) ?_ hlim
  filter_upwards [hK] with n hn
  have hreal : (n : ℝ) ≤ (K n : ℝ)^2 := by exact_mod_cast hn
  calc
    (n : ℝ)^2 * q ^ K n ≤ ((K n : ℝ)^2)^2 * q ^ K n := by gcongr
    _ = (K n : ℝ)^4 * q ^ K n := by ring

/-- Convert the per-list exponential estimates into a single failure probability tending to zero. -/
theorem failure_tendsto_zero (K : ℕ → ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hK : ∀ᶠ n in atTop, n ≤ (K n)^2) (failure : ℕ → ℝ)
    (nonneg : ∀ n, 0 ≤ failure n)
    (bound : ∀ᶠ n in atTop, failure n ≤ (n : ℝ)^2 * q ^ K n) :
    Tendsto failure atTop (𝓝 0) :=
  squeeze_zero' (Eventually.of_forall nonneg) bound
    (tendsto_zero_of_polynomial_tests K q hq0 hq1 hK)

end SplitGapIII
