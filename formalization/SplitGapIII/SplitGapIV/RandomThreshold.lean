module

public import SplitGapIV.SurvivingLists

@[expose] public section

namespace SplitGapIV

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {Ω V H : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [DecidableEq V] [Fintype H] [DecidableEq H]

/-- Chernoff base for a lower tail at one quarter of the mean. -/
theorem quarter_mean_factor_le (r : ℝ) (hr : 0 ≤ r) :
    Real.exp (r/4) * (1-r+r*Real.exp (-1)) ≤ Real.exp (-r/4) := by
  have hhalf : Real.exp (-1) ≤ 1/2 := by
    rw [Real.exp_neg, inv_eq_one_div,
      div_le_div_iff₀ (Real.exp_pos 1) (by norm_num : (0:ℝ) < 2)]
    linarith [Real.exp_one_gt_two]
  have hb : 1-r+r*Real.exp (-1) ≤ Real.exp (-r/2) := by
    linarith [mul_le_mul_of_nonneg_left hhalf hr, Real.add_one_le_exp (-r/2)]
  calc
    _ ≤ Real.exp (r/4) * Real.exp (-r/2) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

private theorem list_lower_tail (N : H → Finset V) (keep : H × V → Set Ω)
    (hm : ∀ x, MeasurableSet (keep x)) (hind : iIndepSet keep μ)
    (p : ℝ≥0∞) (hp : ∀ x, μ (keep x) = p) (hp1 : p.toReal ≤ 1)
    (e : Finset V) (he : e.card = 2) (L : ℕ)
    (hL : (L : ℝ) ≤ p.toReal^2 * (availableHosts N e).card / 4) :
    μ.real {ω | (availableHosts (live N keep ω) e).card < L} ≤
      Real.exp (-p.toReal^2 * (availableHosts N e).card / 4) := by
  classical
  let S := availableHosts N e
  let ports (h : H) := e.image fun v => (h,v)
  let A (h : H) : Set Ω := ⋂ r ∈ ports h, keep r
  have himage (h : H) : (ports h).card = 2 := by
    rw [show ports h = e.image (fun v => (h,v)) from rfl,
      card_image_of_injective _ (fun _ _ eq => (Prod.mk.inj eq).2), he]
  have hsep : ∀ i j, i ≠ j → Disjoint (ports i) (ports j) := by
    intro i j h
    refine disjoint_left.mpr fun t ht ht' => ?_
    obtain ⟨a, _, ha⟩ := mem_image.mp ht
    obtain ⟨b, _, hb⟩ := mem_image.mp ht'
    exact h (congrArg Prod.fst (ha.trans hb.symm))
  have hcount (ω : Ω) :
      (∑ h ∈ S, (A h).indicator (fun _ => (1 : ℝ)) ω) =
        (availableHosts (live N keep ω) e).card := by
    have hsets : S.filter (fun h => ω ∈ A h) = availableHosts (live N keep ω) e := by
      ext h
      have hA : ω ∈ A h ↔ ∀ v ∈ e, ω ∈ keep (h,v) := by
        constructor
        · intro hω v hv
          exact Set.mem_iInter₂.mp hω (h,v) (mem_image.mpr ⟨v,hv,rfl⟩)
        · intro hω
          refine Set.mem_iInter₂.mpr fun r hr => ?_
          obtain ⟨v,hv,rfl⟩ := mem_image.mp hr
          exact hω v hv
      simp only [S, availableHosts, mem_filter, mem_univ, true_and, hA, subset_iff, mem_live]
      grind
    rw [show (∑ h ∈ S, (A h).indicator (fun _ => (1 : ℝ)) ω) =
      ((S.filter fun h => ω ∈ A h).card : ℝ) by
      simp [Set.indicator_apply]]
    rw [hsets]
  have hsub : {ω | (availableHosts (live N keep ω) e).card < L} ⊆
      {ω | (∑ h ∈ S, (A h).indicator (fun _ => (1 : ℝ)) ω) ≤
        p.toReal^2/4 * S.card} := by
    intro ω hω
    rw [Set.mem_ofPred_eq, hcount]
    have hh : ((availableHosts (live N keep ω) e).card : ℝ) ≤ L := by
      exact_mod_cast (Nat.le_of_lt hω)
    exact hh.trans (by simpa only [S, div_mul_eq_mul_div] using hL)
  have htail := SplitGapIII.survival_lower_tail S A
    (fun h => Finset.measurableSet_biInter _ fun r _ => hm r)
    (SplitGapIII.independent_host_survival ports keep hm hind hsep).iIndepFun_indicator
    (p.toReal^2) (p.toReal^2/4) (-1) (by norm_num)
    (fun h _ => SplitGapIII.measure_host_survival (ports h) keep hind (himage h) p
      (fun r _ => hp r))
  apply (measureReal_mono hsub (measure_ne_top μ _)).trans
  apply htail.trans
  have hx0 : 0 ≤ p.toReal^2 := sq_nonneg _
  have hx1 : p.toReal^2 ≤ 1 := by nlinarith [ENNReal.toReal_nonneg (a := p)]
  calc
    _ ≤ (Real.exp (-(p.toReal^2)/4)) ^ S.card := by
      apply pow_le_pow_left₀
      · exact mul_nonneg (Real.exp_pos _).le (by positivity [sub_nonneg.mpr hx1])
      · norm_num
        exact quarter_mean_factor_le _ hx0
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; dsimp [S]; ring

private theorem neighborhood_upper_tail (N : H → Finset V) (keep : H × V → Set Ω)
    (hm : ∀ x, MeasurableSet (keep x)) (hind : iIndepSet keep μ)
    (p : ℝ≥0∞) (hp : ∀ x, μ (keep x) = p) (hp1 : p.toReal ≤ 1) (h : H) (b : ℕ) :
    μ.real {ω | b < (live N keep ω h).card} ≤
      Real.exp (2*p.toReal*(N h).card-b) := by
  classical
  by_cases hN : (N h).card = 0
  · have hs : {ω | b < (live N keep ω h).card} = ∅ := by
      ext ω
      have hz : N h = ∅ := card_eq_zero.mp hN
      simp [live,hz]
    rw [hs,measureReal_empty]
    positivity
  let k := (N h).card
  have hk : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  let a : ℝ := 1 - (b : ℝ)/(k : ℝ)
  let K : V → Set Ω := fun v => keep (h,v)
  have hind' : iIndepSet K μ :=
    hind.precomp (g := fun v : V => (h,v)) (fun _ _ eq => (Prod.mk.inj eq).2)
  have hsub : {ω | b < (live N keep ω h).card} ⊆
      {ω | (∑ v ∈ N h, (K v)ᶜ.indicator (fun _ => (1 : ℝ)) ω) ≤ a * k} := by
    intro ω hω
    rw [Set.mem_ofPred_eq]
    have hsum : (∑ v ∈ N h, (K v)ᶜ.indicator (fun _ => (1 : ℝ)) ω) =
        (((N h).filter fun v => ω ∉ keep (h,v)).card : ℝ) := by
      calc
        _ = ∑ v ∈ (N h).filter (fun v => ω ∈ (K v)ᶜ), (1:ℝ) := by
          rw [sum_filter]
          simp only [Set.indicator_apply]
        _ = _ := by simp [K]
    rw [hsum]
    have heq : ((live N keep ω h).card : ℝ) + ((N h).filter fun v => ω ∉ keep (h,v)).card = k := by
      exact_mod_cast Finset.card_filter_add_card_filter_not (s := N h) (fun v => ω ∈ keep (h,v))
    have hb : (b : ℝ) ≤ (live N keep ω h).card := by exact_mod_cast (Nat.le_of_lt hω)
    have ha : a*(k : ℝ) = (k : ℝ)-b := by dsimp [a]; field_simp
    rw [ha]
    linarith
  have htail := SplitGapIII.deletion_count_tail (N h) K (fun v => hm (h,v)) hind'
    p.toReal a (-1) (by norm_num) (fun v _ => by simp [K,measureReal_def,hp])
  apply (measureReal_mono hsub (measure_ne_top μ _)).trans
  apply htail.trans
  have hp0 : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have hb : p.toReal+(1-p.toReal)*Real.exp (-1) ≤ Real.exp (-1)*Real.exp (2*p.toReal) := by
    have he := Real.add_one_le_exp (2*p.toReal)
    calc
      _ = Real.exp (-1)*(1+p.toReal*(Real.exp 1-1)) := by
        rw [Real.exp_neg]; field_simp; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        nlinarith [mul_nonneg hp0 (sub_nonneg.mpr Real.exp_one_lt_three.le)]
  calc
    _ ≤ (Real.exp a * (Real.exp (-1) * Real.exp (2*p.toReal))) ^ k := by
      apply pow_le_pow_left₀
      · exact mul_nonneg (Real.exp_pos _).le (add_nonneg hp0 (mul_nonneg (sub_nonneg.mpr hp1) (Real.exp_pos _).le))
      · norm_num
        exact mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_nat_mul]
      congr 1
      have ha : (k : ℝ)*(a-1) = -(b : ℝ) := by dsimp [a]; field_simp; ring
      change (k : ℝ)*(a+(-1+2*p.toReal)) = 2*p.toReal*k-b
      linarith

/-- Exact assignment after independent crossing-edge deletions. The list supply is k,
and W bounds initial host neighborhoods. All weights and budgets refer to physical spokes. -/
theorem recovery_above_threshold
    (J : Finset (Finset V)) (htwo : ∀ e ∈ J, e.card = 2) (N : H → Finset V)
    (keep : H × V → Set Ω) (hm : ∀ x, MeasurableSet (keep x)) (hind : iIndepSet keep μ)
    (p : ℝ≥0∞) (hp : ∀ x, μ (keep x) = p) (hp1 : p.toReal ≤ 1)
    (k W b L : ℕ) (hk : ∀ e ∈ J, k ≤ (availableHosts N e).card)
    (hW : ∀ h, (N h).card ≤ W) (hL : 0 < L) (hbudget : 24*b ≤ L)
    (hmean : (L : ℝ) ≤ p.toReal^2*k/4) (u : ℝ)
    (hu : u ≤ p.toReal^2*k/4) (hb : u+2*p.toReal*W ≤ b) :
    μ.real (recovery J N keep)ᶜ ≤
      ((J.card : ℝ) + Fintype.card H)*Real.exp (-u) := by
  classical
  let A (e : Finset V) : Set Ω := {ω | (availableHosts (live N keep ω) e).card < L}
  let B (h : H) : Set Ω := {ω | b < (live N keep ω h).card}
  have hsub : (recovery J N keep)ᶜ ⊆
      (⋃ e ∈ J, A e) ∪ (⋃ h ∈ (univ : Finset H), B h) := by
    intro ω hω
    by_contra hn
    apply hω
    apply assigned_of_surviving_lists J _ htwo hL hbudget
    · intro e he
      exact le_of_not_gt fun h => hn (Or.inl (Set.mem_iUnion₂.mpr ⟨e,he,h⟩))
    · intro h
      exact le_of_not_gt fun hh => hn (Or.inr (Set.mem_iUnion₂.mpr ⟨h,mem_univ _,hh⟩))
  apply (measureReal_mono hsub (measure_ne_top μ _)).trans
  apply (measureReal_union_le _ _).trans
  have hA : μ.real (⋃ e ∈ J, A e) ≤ (J.card : ℝ)*Real.exp (-u) := by
    apply (measureReal_biUnion_finset_le _ _).trans
    calc
      _ ≤ ∑ _e ∈ J, Real.exp (-u) := by
        apply sum_le_sum
        intro e he
        have hmu : p.toReal^2*(k : ℝ) ≤ p.toReal^2*(availableHosts N e).card :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hk e he) (sq_nonneg _)
        apply (list_lower_tail N keep hm hind p hp hp1 e (htwo e he) L (by linarith)).trans
        exact Real.exp_le_exp.mpr (by linarith)
      _ = _ := by simp [nsmul_eq_mul]
  have hB : μ.real (⋃ h ∈ (univ : Finset H), B h) ≤
      (Fintype.card H : ℝ)*Real.exp (-u) := by
    apply (measureReal_biUnion_finset_le _ _).trans
    calc
      _ ≤ ∑ _h : H, Real.exp (-u) := by
        apply sum_le_sum
        intro h _
        have hmu : 2*p.toReal*((N h).card : ℝ) ≤ 2*p.toReal*W :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hW h) (by positivity)
        exact (neighborhood_upper_tail N keep hm hind p hp hp1 h b).trans
          (Real.exp_le_exp.mpr (by linarith))
      _ = _ := by simp [nsmul_eq_mul]
  rw [add_mul]
  exact add_le_add hA hB

end SplitGapIV
