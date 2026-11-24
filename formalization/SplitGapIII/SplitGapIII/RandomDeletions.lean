module

public import Mathlib.Probability.Moments.Basic
public import Mathlib.Analysis.Calculus.DerivativeTest
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

namespace SplitGapIII
open Finset MeasureTheory ProbabilityTheory Real
open scoped BigOperators ENNReal Topology

variable {Ω E I : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable [IsProbabilityMeasure μ]

/-- The exponential moment of a one-bit survival event. -/
theorem mgf_survival_event (A : Set Ω) (hA : MeasurableSet A) (t : ℝ) :
    mgf (A.indicator (fun _ => (1 : ℝ))) μ t =
      1 - μ.real A + μ.real A * exp t := by
  classical
  have hexp : (fun ω => exp (t * A.indicator (fun _ => (1 : ℝ)) ω)) =
      A.indicator (fun _ => exp t) + Aᶜ.indicator (fun _ => (1 : ℝ)) := by
    funext ω
    by_cases h : ω ∈ A <;> simp [h, Set.indicator_of_mem, Set.indicator_of_notMem]
  rw [mgf, hexp]
  change (∫ ω, A.indicator (fun _ => exp t) ω + Aᶜ.indicator (fun _ => (1 : ℝ)) ω ∂μ) = _
  rw [integral_add ((integrable_const _).indicator hA)
    ((integrable_const _).indicator hA.compl), integral_indicator hA,
    integral_indicator hA.compl, setIntegral_const, setIntegral_const, measureReal_compl hA]
  simp [smul_eq_mul]
  ring

/-- Simultaneous bounds use independence only within each list of candidate hosts. -/
theorem measure_fails_le_sum_of_tails (tests : Finset E) (X : E → Ω → ℝ) (target : E → ℝ)
    (Good : Set Ω) (recover : ∀ ω, (∀ e ∈ tests, target e < X e ω) → ω ∈ Good)
    (bound : E → ℝ) (tails : ∀ e ∈ tests, μ.real {ω | X e ω ≤ target e} ≤ bound e) :
    μ.real Goodᶜ ≤ ∑ e ∈ tests, bound e := by
  classical
  let bad (e : E) := {ω | X e ω ≤ target e}
  have sub : Goodᶜ ⊆ ⋃ e ∈ tests, bad e := by
    intro ω hω
    by_contra hh
    apply hω
    apply recover
    intro e he
    exact lt_of_not_ge fun h => hh (Set.mem_iUnion₂.mpr ⟨e, he, h⟩)
  exact (measureReal_mono sub (measure_ne_top μ _)).trans
    ((measureReal_biUnion_finset_le tests bad).trans (sum_le_sum tails))

/-- The Chernoff factor for a finite independent family of surviving candidates. -/
theorem survival_lower_tail (hosts : Finset I) (A : I → Set Ω)
    (hA : ∀ h, MeasurableSet (A h))
    (independent : iIndepFun (fun h => (A h).indicator (fun _ => (1 : ℝ))) μ)
    (prob a t : ℝ) (ht : t ≤ 0) (hprob : ∀ h ∈ hosts, μ.real (A h) = prob) :
    μ.real {ω | (∑ h ∈ hosts, (A h).indicator (fun _ => (1 : ℝ)) ω) ≤ a * hosts.card} ≤
      (exp (-t * a) * (1 - prob + prob * exp t)) ^ hosts.card := by
  classical
  let X (h : I) := (A h).indicator (fun _ => (1 : ℝ))
  have hx : ∀ h, Measurable (X h) := fun h => measurable_const.indicator (hA h)
  have h_int : ∀ h ∈ hosts, Integrable (fun ω => exp (t * X h ω)) μ := by
    intro h _
    have hexp : (fun ω => exp (t * X h ω)) =
        (A h).indicator (fun _ => exp t) + (A h)ᶜ.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases hm : ω ∈ A h <;> simp [X, hm, Set.indicator_of_mem, Set.indicator_of_notMem]
    rw [hexp]
    exact ((integrable_const _).indicator (hA h)).add ((integrable_const _).indicator (hA h).compl)
  have hbound := measure_le_le_exp_mul_mgf (μ := μ) (X := ∑ h ∈ hosts, X h)
    (a * hosts.card) ht (independent.integrable_exp_mul_sum hx h_int)
  rw [independent.mgf_sum hx, Finset.prod_eq_pow_card (fun h hh => by
    rw [mgf_survival_event _ (hA h), hprob h hh])] at hbound
  rw [mul_pow, ← Real.exp_nat_mul, show (hosts.card : ℝ) * (-t * a) =
    -t * (a * hosts.card) by ring]
  simpa only [X, Finset.sum_apply] using hbound

/-- Events obtained from disjoint sets of physical incidences remain independent. -/
theorem independent_host_survival {R : Type*} [DecidableEq R]
    (ports : I → Finset R) (keep : R → Set Ω)
    (keepMeasurable : ∀ r, MeasurableSet (keep r)) (keepIndependent : iIndepSet keep μ)
    (portDisjoint : ∀ i j, i ≠ j → Disjoint (ports i) (ports j)) :
    iIndepSet (fun h => ⋂ r ∈ ports h, keep r) μ := by
  classical
  let A (h : I) := ⋂ r ∈ ports h, keep r
  have hA (h : I) : MeasurableSet (A h) :=
    Finset.measurableSet_biInter _ fun r _ => keepMeasurable r
  apply (iIndepSet_iff_meas_biInter hA).2
  intro s
  have heq : (⋂ h ∈ s, A h) = ⋂ r ∈ s.biUnion ports, keep r := by
    ext ω
    simp only [Set.mem_iInter, mem_biUnion, A]
    constructor
    · intro h r hr
      obtain ⟨i, hi, hir⟩ := hr
      exact h i hi r hir
    · intro h i hi r hr
      exact h r ⟨i, hi, hr⟩
  rw [heq, keepIndependent.meas_biInter, Finset.prod_biUnion]
  · simp_rw [A, keepIndependent.meas_biInter]
  · exact fun i _ j _ hij => portDisjoint i j hij

/-- Per-candidate survival is the product of the two physical spoke probabilities. -/
theorem measure_host_survival {R : Type*} (ports : Finset R) (keep : R → Set Ω)
    (keepIndependent : iIndepSet keep μ)
    (twoPorts : ports.card = 2) (p : ℝ≥0∞) (hp : ∀ r ∈ ports, μ (keep r) = p) :
    μ.real (⋂ r ∈ ports, keep r) = p.toReal ^ 2 := by
  rw [measureReal_def, keepIndependent.meas_biInter,
    Finset.prod_eq_pow_card hp, twoPorts, ENNReal.toReal_pow]

/-- A fixed fractional slack produces a Chernoff base strictly below one. -/
theorem exists_strict_tail_factor (prob a : ℝ) (h : a < prob) :
    ∃ t : ℝ, t < 0 ∧ exp (-t * a) * (1 - prob + prob * exp t) < 1 := by
  let F (u : ℝ) := exp (u * a) * (1 - prob + prob * exp (-u)) - 1
  have hd : HasDerivAt F (a - prob) 0 := by
    have hl := ((hasDerivAt_id (0 : ℝ)).mul_const a).exp
    have hr := (((hasDerivAt_id (0 : ℝ)).neg.exp).const_mul prob).const_add (1 - prob)
    convert (hl.mul hr).sub_const 1 using 1 <;> simp [F] <;> ring
  have h0 : F 0 = 0 := by simp [F]
  have hs := eventually_nhdsWithin_sign_eq_of_deriv_neg (by rw [hd.deriv]; linarith) h0
  have hpos : ∀ᶠ u : ℝ in 𝓝[>] 0, 0 < u := self_mem_nhdsWithin
  have hnear : ∀ᶠ u : ℝ in 𝓝[>] 0, 0 < u ∧ F u < 0 := by
    filter_upwards [hs.filter_mono nhdsWithin_le_nhds, hpos] with u hu hu0
    refine ⟨hu0, sign_eq_neg_one_iff.mp ?_⟩
    rw [hu, sign_neg (sub_neg.mpr hu0)]
  obtain ⟨u, hu, huF⟩ := hnear.exists
  refine ⟨-u, neg_neg_of_pos hu, ?_⟩
  simpa [F, sub_neg] using huF

/-- A finite simultaneous bound for all classes of requests under independent deletions.
Different requests may reuse the same random incidences in their lists. -/
theorem physical_survival_bound
    {R : Type*} [DecidableEq R]
    (tests : Finset E) (hosts : E → Finset I) (ports : E → I → Finset R)
    (keep : R → Set Ω) (keepMeasurable : ∀ r, MeasurableSet (keep r))
    (keepIndependent : iIndepSet keep μ) (p : ℝ≥0∞)
    (probability : ∀ r, μ (keep r) = p)
    (two : ∀ e h, (ports e h).card = 2)
    (separate : ∀ e i j, i ≠ j → Disjoint (ports e i) (ports e j))
    (a t : ℝ) (ht : t ≤ 0)
    (Good : Set Ω)
    (recover : ∀ ω, (∀ e ∈ tests, a * (hosts e).card <
      ∑ h ∈ hosts e, (⋂ r ∈ ports e h, keep r).indicator (fun _ => (1 : ℝ)) ω) → ω ∈ Good) :
    μ.real Goodᶜ ≤
      ∑ e ∈ tests, (exp (-t * a) * (1 - p.toReal ^ 2 + p.toReal ^ 2 * exp t)) ^ (hosts e).card := by
  classical
  let A (e : E) (h : I) := ⋂ r ∈ ports e h, keep r
  refine measure_fails_le_sum_of_tails tests
    (fun e ω => ∑ h ∈ hosts e, (A e h).indicator (fun _ => (1 : ℝ)) ω)
    (fun e => a * (hosts e).card) Good recover _ ?_
  intro e _
  exact survival_lower_tail (hosts e) (A e)
    (fun h => Finset.measurableSet_biInter (ports e h) fun r _ => keepMeasurable r)
    (independent_host_survival (ports e) keep keepMeasurable keepIndependent
      (separate e)).iIndepFun_indicator
    (p.toReal ^ 2) a t ht
    (fun h _ => measure_host_survival (ports e h) keep keepIndependent (two e h) p
      (fun r _ => probability r))

/-- The same coin law also controls the number of edges actually deleted.
This lower tail, with the trivial upper bound by the edge count, yields quadratic deletion counts
when the number of crossing incidences is quadratic. -/
theorem deletion_count_tail (edges : Finset I) (keep : I → Set Ω)
    (measurableKeep : ∀ i, MeasurableSet (keep i)) (independentKeep : iIndepSet keep μ)
    (prob a t : ℝ) (ht : t ≤ 0) (same : ∀ i ∈ edges, μ.real (keep i) = prob) :
    μ.real {ω | (∑ i ∈ edges, (keep i)ᶜ.indicator (fun _ => (1 : ℝ)) ω) ≤ a * edges.card} ≤
      (exp (-t * a) * (prob + (1 - prob) * exp t)) ^ edges.card := by
  classical
  let K (i : I) := (keep i).indicator (fun _ => (1 : ℝ))
  have hi : iIndepFun K μ := independentKeep.iIndepFun_indicator
  let flip (x : ℝ) := 1 - x
  have hf : Measurable flip := measurable_const.sub measurable_id
  have hd : iIndepFun (fun i ω => 1 - K i ω) μ := by
    simpa only [Function.comp_def, flip] using hi.comp (fun _ : I => flip) (fun _ => hf)
  have eq : (fun i ω => 1 - K i ω) = fun i => (keep i)ᶜ.indicator (fun _ => (1 : ℝ)) := by
    funext i ω
    by_cases h : ω ∈ keep i <;> simp [K, h]
  rw [eq] at hd
  have h := survival_lower_tail edges (fun i => (keep i)ᶜ) (fun i => (measurableKeep i).compl)
    hd (1 - prob) a t ht (fun i hi => by rw [measureReal_compl (measurableKeep i), same i hi]; simp)
  convert h using 2
  ring

end SplitGapIII
