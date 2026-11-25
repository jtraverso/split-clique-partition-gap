module

public import SplitGapIII.RandomDeletions
public import SplitGapIII.Reassignment
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace SplitGapIV

open Finset MeasureTheory ProbabilityTheory GapExtremal QuadraticExteriorPalomar SplitGapIII
open scoped BigOperators ENNReal

variable {Ω V H U E : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

private theorem measure_port_inter [DecidableEq E]
    (keep : U → Set Ω) (hm : ∀ u, MeasurableSet (keep u)) (hi : iIndepSet keep μ)
    (ports : E → Set U) (A : E → Set Ω) (s : Finset E)
    (hd : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (ports i) (ports j))
    (hA : ∀ i ∈ s, MeasurableSet[MeasurableSpace.generateFrom
      {t | ∃ u ∈ ports i, keep u = t}] (A i)) :
    μ (⋂ i ∈ s, A i) = ∏ i ∈ s, μ (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    rw [Finset.set_biInter_insert, Finset.prod_insert his]
    have hstep := ih (fun j hj k hk => hd j (mem_insert_of_mem hj) k (mem_insert_of_mem hk))
      (fun j hj => hA j (mem_insert_of_mem hj))
    rw [← hstep]
    have hd' : Disjoint (ports i) (⋃ j ∈ s, ports j) := by
      refine Set.disjoint_left.mpr ?_
      intro u hu hu'
      obtain ⟨j, hj, hj'⟩ := Set.mem_iUnion₂.mp hu'
      exact Set.disjoint_left.mp (hd i (mem_insert_self ..) j (mem_insert_of_mem hj)
        (fun eq => his (eq ▸ hj))) hu hj'
    have hB : MeasurableSet[MeasurableSpace.generateFrom
        {t | ∃ u ∈ ⋃ j ∈ s, ports j, keep u = t}] (⋂ j ∈ s, A j) := by
      refine Finset.measurableSet_biInter _ fun j hj => ?_
      have hle : {t | ∃ u ∈ ports j, keep u = t} ⊆
          {t | ∃ u ∈ ⋃ k ∈ s, ports k, keep u = t} := by
        rintro t ⟨u, hu, rfl⟩
        exact ⟨u, Set.mem_iUnion₂.mpr ⟨j,hj,hu⟩, rfl⟩
      exact (MeasurableSpace.generateFrom_mono hle) _ (hA j (mem_insert_of_mem hj))
    exact (Indep_iff _ _ μ).mp (hi.indep_generateFrom_of_disjoint hm _ _ hd')
      _ _ (hA i (mem_insert_self ..)) hB

variable [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]

/-- The live neighborhood after deleting crossing edges. -/
noncomputable def live (N : H → Finset V) (keep : H × V → Set Ω) (ω : Ω) (h : H) :
    Finset V := by
  classical
  exact (N h).filter fun v => ω ∈ keep (h,v)

omit [MeasurableSpace Ω] [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
theorem mem_live {N : H → Finset V} {keep : H × V → Set Ω} {ω : Ω} {h : H} {v : V} :
    v ∈ live N keep ω h ↔ v ∈ N h ∧ ω ∈ keep (h,v) := by
  classical
  simp [live]

/-- The event of a complete physical assignment on the surviving crossing edges. -/
def recovery (J : Finset (Finset V)) (N : H → Finset V) (keep : H × V → Set Ω) : Set Ω :=
  {ω | ∃ host : J → H, Assigned (live N keep ω) J host}

omit [MeasurableSpace Ω] in
theorem recovery_preserves_gap (B : SimpleGraph V) [DecidableRel B.Adj]
    (N : H → Finset V) (keep : H × V → Set Ω) (ω : Ω)
    (hi : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (hr : ω ∈ recovery (jPairs B univ) N keep) :
    gap (hostGraph (live N keep ω)) = residualSup B - residualInt B := by
  obtain ⟨host, ha⟩ := hr
  exact gap_of_complete_recovery B _ (fun h a ha' b hb' =>
    hi h a (mem_live.mp ha').1 b (mem_live.mp hb').1) host ha

private def candidate (keep : H × V → Set Ω) (e : Finset V) (h : H) : Set Ω :=
  ⋂ v ∈ e, keep (h,v)

private def covered (N : H → Finset V) (keep : H × V → Set Ω) (e : Finset V) : Set Ω :=
  ⋃ h ∈ (univ : Finset H).filter (fun h => e ⊆ N h), candidate keep e h

omit [IsProbabilityMeasure μ] [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] in
private theorem measure_candidate (keep : H × V → Set Ω) (hi : iIndepSet keep μ)
    (p : ℝ≥0∞) (hp : ∀ x, μ (keep x) = p) (e : Finset V) (he : e.card = 2) (h : H) :
    μ (candidate keep e h) = p ^ 2 := by
  have hi' := hi.precomp (g := fun v : V => (h,v)) (fun _ _ eq => (Prod.mk.inj eq).2)
  change μ (⋂ v ∈ e, (keep ∘ fun v : V => (h,v)) v) = p ^ 2
  rw [hi'.meas_biInter]
  simp [hp, he]

omit [Fintype V] in
private theorem measure_covered (N : H → Finset V) (keep : H × V → Set Ω)
    (hm : ∀ u, MeasurableSet (keep u)) (hi : iIndepSet keep μ)
    (p : ℝ≥0∞) (hp : ∀ x, μ (keep x) = p) (e : Finset V) (he : e.card = 2) :
    μ.real (covered N keep e) = 1 - (1 - p.toReal ^ 2) ^
      ((univ : Finset H).filter (fun h => e ⊆ N h)).card := by
  classical
  let S := (univ : Finset H).filter (fun h => e ⊆ N h)
  let ports (h : H) : Set (H × V) := {u | u.1 = h ∧ u.2 ∈ e}
  have hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (ports i) (ports j) := by
    intro i _ j _ hij
    exact Set.disjoint_left.mpr fun u hu hv => hij (hu.1.symm.trans hv.1)
  have hmeas (h : H) : MeasurableSet (candidate keep e h) :=
    Finset.measurableSet_biInter _ fun v _ => hm (h,v)
  have hlocal : ∀ h ∈ S, MeasurableSet[MeasurableSpace.generateFrom
      {t | ∃ u ∈ ports h, keep u = t}] (candidate keep e h)ᶜ := by
    intro h _
    apply MeasurableSet.compl
    exact Finset.measurableSet_biInter _ fun v hv =>
      MeasurableSpace.measurableSet_generateFrom ⟨(h,v), ⟨rfl,hv⟩, rfl⟩
  have hB : MeasurableSet (covered N keep e) :=
    Finset.measurableSet_biUnion _ fun h _ => hmeas h
  have heq : (covered N keep e)ᶜ = ⋂ h ∈ S, (candidate keep e h)ᶜ := by
    ext ω
    simp [covered, S]
  have hprod := measure_port_inter keep hm hi ports (fun h => (candidate keep e h)ᶜ) S hsep hlocal
  have hreal := congrArg ENNReal.toReal hprod
  rw [← heq, ENNReal.toReal_prod] at hreal
  change μ.real (covered N keep e)ᶜ = ∏ h ∈ S, μ.real (candidate keep e h)ᶜ at hreal
  have hterm (h : H) : μ.real (candidate keep e h)ᶜ = 1 - p.toReal ^ 2 := by
    rw [measureReal_compl (hmeas h)]
    simp [measureReal_def, measure_candidate keep hi p hp e he]
  rw [measureReal_compl hB] at hreal
  simp_rw [hterm, Finset.prod_const] at hreal
  rw [show μ.real Set.univ = 1 by simp [measureReal_def]] at hreal
  change μ.real (covered N keep e) = 1 - (1 - p.toReal ^ 2) ^ S.card
  linarith

/-- A common budget of initial hosts suffices for all lists to be nonempty.
Independence is required within a list, but lists for different requests may share spokes. -/
theorem empty_list_probability (J : Finset (Finset V)) (htwo : ∀ e ∈ J, e.card = 2)
    (N : H → Finset V) (keep : H × V → Set Ω)
    (hm : ∀ u, MeasurableSet (keep u)) (hi : iIndepSet keep μ)
    (p : ℝ≥0∞) (hp : ∀ x, μ (keep x) = p) (hp1 : p.toReal ≤ 1)
    (k : ℕ) (hk : ∀ e ∈ J, k ≤ ((univ : Finset H).filter (fun h => e ⊆ N h)).card) :
    μ.real {ω | ∃ e ∈ J, ¬ ∃ h, e ⊆ live N keep ω h} ≤
      (J.card : ℝ) * Real.exp (-p.toReal^2 * k) := by
  classical
  have heq : {ω | ∃ e ∈ J, ¬ ∃ h, e ⊆ live N keep ω h} =
      ⋃ e ∈ J, (covered N keep e)ᶜ := by
    ext ω
    constructor
    · rintro ⟨e, he, hnone⟩
      refine Set.mem_iUnion₂.mpr ⟨e, he, ?_⟩
      intro hc
      obtain ⟨h, hh, hc⟩ := Set.mem_iUnion₂.mp hc
      exact hnone ⟨h, fun v hv => mem_live.mpr
        ⟨(mem_filter.mp hh).2 hv, Set.mem_iInter₂.mp hc v hv⟩⟩
    · intro hω
      obtain ⟨e, he, hnone⟩ := Set.mem_iUnion₂.mp hω
      refine ⟨e, he, ?_⟩
      rintro ⟨h, hh⟩
      apply hnone
      exact Set.mem_iUnion₂.mpr ⟨h, mem_filter.mpr ⟨mem_univ _, fun v hv =>
        (mem_live.mp (hh hv)).1⟩, Set.mem_iInter₂.mpr fun v hv => (mem_live.mp (hh hv)).2⟩
  rw [heq]
  apply (measureReal_biUnion_finset_le J _).trans
  have hq0 : 0 ≤ 1 - p.toReal^2 := by nlinarith [ENNReal.toReal_nonneg (a := p)]
  have hq1 : 1 - p.toReal^2 ≤ 1 := by nlinarith
  calc
    _ ≤ ∑ _e ∈ J, Real.exp (-p.toReal^2 * k) := by
      apply sum_le_sum
      intro e he
      have hmeas : MeasurableSet (covered N keep e) := Finset.measurableSet_biUnion _
        fun h _ => Finset.measurableSet_biInter _ fun v _ => hm (h,v)
      rw [measureReal_compl hmeas, show μ.real Set.univ = 1 by simp [measureReal_def],
        measure_covered N keep hm hi p hp e (htwo e he)]
      simp only [sub_sub_cancel]
      apply (pow_le_pow_of_le_one hq0 hq1 (hk e he)).trans
      have hbase : 1 - p.toReal^2 ≤ Real.exp (-p.toReal^2) := by
        linarith [Real.add_one_le_exp (-p.toReal^2)]
      calc
        _ ≤ Real.exp (-p.toReal^2) ^ k := pow_le_pow_left₀ hq0 hbase _
        _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ = _ := by simp [nsmul_eq_mul]

/-- The failure probabilities for vertex-disjoint requests multiply on their physical spokes. -/
theorem matching_recovery_bound (J M : Finset (Finset V)) (hsub : M ⊆ J)
    (hdis : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f)
    (htwo : ∀ e ∈ M, e.card = 2)
    (N : H → Finset V) (keep : H × V → Set Ω)
    (hm : ∀ u, MeasurableSet (keep u)) (hi : iIndepSet keep μ)
    (p : ℝ≥0∞) (hp : ∀ x, μ (keep x) = p) (hp1 : p.toReal ≤ 1) :
    μ.real (recovery J N keep) ≤
      Real.exp (-((M.card : ℝ) * (1 - p.toReal ^ 2) ^ Fintype.card H)) := by
  classical
  let ports (e : Finset V) : Set (H × V) := {u | u.2 ∈ e}
  have hsep : ∀ i ∈ M, ∀ j ∈ M, i ≠ j → Disjoint (ports i) (ports j) := by
    intro i hi' j hj hij
    exact Set.disjoint_left.mpr fun u hu hv => disjoint_left.mp (hdis i hi' j hj hij) hu hv
  have hlocal : ∀ e ∈ M, MeasurableSet[MeasurableSpace.generateFrom
      {t | ∃ u ∈ ports e, keep u = t}] (covered N keep e) := by
    intro e _
    exact Finset.measurableSet_biUnion _ fun h _ => Finset.measurableSet_biInter _ fun v hv =>
      MeasurableSpace.measurableSet_generateFrom ⟨(h,v), hv, rfl⟩
  have hs : recovery J N keep ⊆ ⋂ e ∈ M, covered N keep e := by
    intro ω hω
    obtain ⟨host, ha⟩ := hω
    refine Set.mem_iInter₂.mpr fun e he => ?_
    let r : J := ⟨e, hsub he⟩
    exact Set.mem_iUnion₂.mpr ⟨host r,
      mem_filter.mpr ⟨mem_univ _, fun v hv => (mem_live.mp (ha.1 r hv)).1⟩,
      Set.mem_iInter₂.mpr fun v hv => (mem_live.mp (ha.1 r hv)).2⟩
  apply (measureReal_mono hs (measure_ne_top μ _)).trans
  have heq := congrArg ENNReal.toReal
    (measure_port_inter keep hm hi ports (covered N keep) M hsep hlocal)
  rw [ENNReal.toReal_prod] at heq
  change μ.real (⋂ e ∈ M, covered N keep e) = ∏ e ∈ M, μ.real (covered N keep e) at heq
  rw [heq]
  let q := 1 - p.toReal ^ 2
  have hq0 : 0 ≤ q := by dsimp [q]; nlinarith [ENNReal.toReal_nonneg (a := p)]
  have hq1 : q ≤ 1 := by dsimp [q]; nlinarith
  calc
    _ ≤ ∏ _e ∈ M, Real.exp (-(q ^ Fintype.card H)) := by
      apply prod_le_prod₀ (fun _ _ => measureReal_nonneg)
      intro e he
      rw [measure_covered N keep hm hi p hp e (htwo e he)]
      have hl : ((univ : Finset H).filter (fun h => e ⊆ N h)).card ≤ Fintype.card H :=
        card_le_univ _
      have hpow := pow_le_pow_of_le_one hq0 hq1 hl
      apply le_trans _ (Real.add_one_le_exp (-(q ^ Fintype.card H)))
      dsimp [q] at hpow
      linarith
    _ = _ := by rw [prod_const, ← Real.exp_nat_mul]; congr 1; ring

/-- Finite lower-threshold bound for a polynomial-sized matching of requests.
With r requests in the matching and hp² well below one half of log r, recovery vanishes. -/
theorem recovery_below_threshold (J M : Finset (Finset V)) (hsub : M ⊆ J)
    (hdis : ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f)
    (htwo : ∀ e ∈ M, e.card = 2)
    (N : H → Finset V) (keep : H × V → Set Ω)
    (hm : ∀ u, MeasurableSet (keep u)) (hi : iIndepSet keep μ)
    (p : ℝ≥0∞) (hp : ∀ x, μ (keep x) = p) (hp2 : p.toReal ^ 2 ≤ 1/2)
    (a : ℝ) (ha : 2 * (Fintype.card H : ℝ) * p.toReal ^ 2 ≤ a) :
    μ.real (recovery J N keep) ≤
      Real.exp (-((M.card : ℝ) * Real.exp (-a))) := by
  have hp1 : p.toReal ≤ 1 := by nlinarith [ENNReal.toReal_nonneg (a := p)]
  apply (matching_recovery_bound J M hsub hdis htwo N keep hm hi p hp hp1).trans
  let x := p.toReal ^ 2
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1/2 := hp2
  have hq : 0 < 1 - x := by linarith
  have hrec := Real.log_le_sub_one_of_pos (one_div_pos.mpr hq)
  rw [Real.log_div one_ne_zero hq.ne', Real.log_one, zero_sub] at hrec
  have hdiv : 1 / (1 - x) ≤ 1 + 2*x := by
    apply (div_le_iff₀ hq).2
    nlinarith [mul_nonneg hx0 (show 0 ≤ 1 - 2*x by linarith)]
  have hlog : -2*x ≤ Real.log (1-x) := by linarith
  have hmass : Real.exp (-a) ≤ (1 - p.toReal ^ 2) ^ Fintype.card H := by
    change _ ≤ (1 - x) ^ Fintype.card H
    rw [← Real.exp_log hq, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hax : 2 * (Fintype.card H : ℝ) * x ≤ a := ha
    exact (by linarith : -a ≤ (Fintype.card H : ℝ) * (-2*x)).trans
      (mul_le_mul_of_nonneg_left hlog (by positivity))
  exact Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hmass (by positivity)))

end SplitGapIV
