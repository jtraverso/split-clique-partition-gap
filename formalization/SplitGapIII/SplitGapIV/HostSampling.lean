module

public import SplitGapIV.RandomThreshold

@[expose] public section

namespace SplitGapIV

open Finset MeasureTheory ProbabilityTheory GapExtremal QuadraticExteriorPalomar
open scoped ENNReal

variable {T V H : Type*}
variable [MeasurableSpace T] [Fintype H] [DecidableEq H] [DecidableEq V]

/-- A distribution over palettes yields a fixed finite family with all required lists large. -/
theorem exists_palettes_of_distribution (ν : Measure T) [IsProbabilityMeasure ν]
    (P : T → Finset V) (J : Finset (Finset V))
    (hm : ∀ e ∈ J, MeasurableSet {t | e ⊆ P t})
    (η : ℝ) (hη : ∀ e ∈ J, η ≤ ν.real {t | e ⊆ P t}) (k : ℕ)
    (hk : (k : ℝ) ≤ η*(Fintype.card H)/4)
    (hbudget : (J.card : ℝ)*Real.exp (-η*(Fintype.card H)/4) < 1) :
    ∃ choice : H → T, ∀ e ∈ J, k ≤ (availableHosts (P ∘ choice) e).card := by
  classical
  let νs : H → Measure T := fun _ => ν
  let μ := Measure.pi νs
  have : ∀ h, IsProbabilityMeasure (νs h) := inferInstance
  have : IsProbabilityMeasure μ := inferInstance
  let X (h : H) (ω : H → T) := ω h
  have hX : iIndepFun X μ := iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  let Good : Set (H → T) := {ω | ∀ e ∈ J, k ≤ (availableHosts (P ∘ ω) e).card}
  let bad (e : Finset V) : Set (H → T) := {ω | (availableHosts (P ∘ ω) e).card < k}
  have heq : Goodᶜ = ⋃ e ∈ J, bad e := by
    ext ω
    simp [Good,bad,not_le]
  have htail (e : Finset V) (he : e ∈ J) :
      μ.real (bad e) ≤ Real.exp (-η * Fintype.card H/4) := by
    let E : Set T := {t | e ⊆ P t}
    let A (h : H) : Set (H → T) := X h ⁻¹' E
    let r := ν.real E
    have hrη : η ≤ r := hη e he
    have hr0 : 0 ≤ r := measureReal_nonneg
    have hr1 : r ≤ 1 := (measureReal_mono (Set.subset_univ _) (measure_ne_top ν _)).trans
      (by simp [measureReal_def])
    have hA (h : H) : MeasurableSet (A h) := (hm e he).preimage (measurable_pi_apply h)
    have hprob (h : H) : μ.real (A h) = r := by
      unfold A
      rw [measureReal_def, ← Measure.map_apply (measurable_pi_apply h) (hm e he)]
      change ((Measure.pi νs).map (Function.eval h) E).toReal = r
      rw [Measure.pi_map_eval]
      have huniv (j : H) : νs j Set.univ = 1 := measure_univ
      simp only [huniv, Finset.prod_const_one, one_smul]
      rfl
    have hI : iIndepFun (fun h => (A h).indicator (fun _ => (1 : ℝ))) μ := by
      have hf : Measurable (E.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator (hm e he)
      have hEq : (fun h => (A h).indicator (fun _ => (1 : ℝ))) =
          (fun h => E.indicator (fun _ => (1 : ℝ)) ∘ X h) := by
        funext h ω
        simp [A, Function.comp_def, Set.indicator_apply]
      rw [hEq]
      exact hX.comp (fun _ => E.indicator (fun _ => (1 : ℝ))) (fun _ => hf)
    have hsub : bad e ⊆ {ω | (∑ h : H, (A h).indicator (fun _ => (1 : ℝ)) ω) ≤
        r/4*Fintype.card H} := by
      intro ω hω
      have hcount : (∑ h : H, (A h).indicator (fun _ => (1 : ℝ)) ω) =
          (availableHosts (P ∘ ω) e).card := by
        simp [Set.indicator_apply,A,E,X,availableHosts]
      rw [Set.mem_ofPred_eq,hcount]
      have hlt : ((availableHosts (P ∘ ω) e).card : ℝ) ≤ k := by
        exact_mod_cast (Nat.le_of_lt hω)
      have hle := mul_le_mul_of_nonneg_right hrη (show 0 ≤ (Fintype.card H : ℝ) by positivity)
      linarith
    apply (measureReal_mono hsub (measure_ne_top μ _)).trans
    apply (SplitGapIII.survival_lower_tail univ A hA hI r (r/4) (-1) (by norm_num)
      (fun h _ => hprob h)).trans
    have hfactor : 0 ≤ Real.exp (r/4)*(1-r+r*Real.exp (-1)) := by
      exact mul_nonneg (Real.exp_pos _).le (add_nonneg (sub_nonneg.mpr hr1) (by positivity))
    calc
      _ ≤ Real.exp (-r/4)^(Fintype.card H) := by
        simp only [card_univ, neg_neg, one_mul]
        exact pow_le_pow_left₀ hfactor (quarter_mean_factor_le r hr0) _
      _ ≤ _ := by
        rw [← Real.exp_nat_mul]
        exact Real.exp_le_exp.mpr (by
          nlinarith [mul_le_mul_of_nonneg_right hrη (show 0 ≤ (Fintype.card H : ℝ) by positivity)])
  have hbad : μ.real Goodᶜ < 1 := by
    rw [heq]
    apply ((measureReal_biUnion_finset_le J bad).trans (sum_le_sum htail)).trans_lt
    simpa [nsmul_eq_mul] using hbudget
  by_contra hn
  have hG : Good = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
  simp [hG,measureReal_def] at hbad

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [Fintype V]

/-- Finite producer: sample the independent palettes once, then recover the exact residual gap
under any independent physical deletion law. -/
theorem exists_exact_gap_recovery_at_supply
    (G : SimpleGraph V) [DecidableRel G.Adj] (ν : Measure T) [IsProbabilityMeasure ν]
    (P : T → Finset V)
    (hI : ∀ t, ∀ a ∈ P t, ∀ b ∈ P t, ¬ G.Adj a b)
    (hm : ∀ e ∈ jPairs G univ, MeasurableSet {t | e ⊆ P t})
    (η : ℝ) (hη : ∀ e ∈ jPairs G univ, η ≤ ν.real {t | e ⊆ P t})
    (p : ℝ≥0∞) (hp1 : p.toReal ≤ 1) (k W b L : ℕ)
    (hk : (k : ℝ) ≤ η*Fintype.card H/4)
    (hbudget : ((jPairs G univ).card : ℝ)*Real.exp (-η*Fintype.card H/4) < 1)
    (hW : ∀ t, (P t).card ≤ W) (hL : 0 < L) (hcap : 24*b ≤ L)
    (hmean : (L : ℝ) ≤ p.toReal^2*k/4)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ p.toReal^2*k/4) (hb : u+2*p.toReal*W ≤ b) :
    ∃ N : H → Finset V, (∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ G.Adj a b) ∧
      gap (hostGraph N) = residualSup G - residualInt G ∧
      ∀ (keep : H × V → Set Ω), (∀ r, MeasurableSet (keep r)) →
        iIndepSet keep μ → (∀ r, μ (keep r) = p) →
        μ.real (recovery (jPairs G univ) N keep)ᶜ ≤
          (((jPairs G univ).card : ℝ)+Fintype.card H)*Real.exp (-u) := by
  classical
  let J := jPairs G univ
  obtain ⟨choice, hchoice⟩ := exists_palettes_of_distribution (H := H) ν P J hm η hη k hk hbudget
  let N := P ∘ choice
  have hind : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ G.Adj a b := fun h => hI (choice h)
  have htwo : ∀ e ∈ J, e.card = 2 := fun _ he => two_of_mem_jPairs he
  have hkp : p.toReal^2*(k : ℝ)/4 ≤ k := by
    have hpr : p.toReal^2 ≤ 1 := by nlinarith [ENNReal.toReal_nonneg (a := p)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hpr) (Nat.cast_nonneg (α := ℝ) k)]
  have hkpos : 0 < k := hL.trans_le (by exact_mod_cast hmean.trans hkp)
  have hpp : 0 < p.toReal := by
    by_contra! hn
    have hz : p.toReal = 0 := le_antisymm hn ENNReal.toReal_nonneg
    rw [hz] at hmean
    have hL' : (0 : ℝ) < L := by exact_mod_cast hL
    norm_num at hmean
    linarith
  have hcapR : 24*(b : ℝ) ≤ L := by exact_mod_cast hcap
  have hscaled : p.toReal * (24*(W : ℝ)) ≤ p.toReal * k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (mul_nonneg hpp.le (Nat.cast_nonneg (α := ℝ) k))]
  have hWk : 24*W ≤ k := by
    exact_mod_cast le_of_mul_le_mul_left hscaled hpp
  obtain ⟨host,hhost⟩ := assigned_of_surviving_lists J N htwo hkpos hWk hchoice
    (fun h => hW (choice h))
  have hgap := SplitGapIII.gap_of_complete_recovery G N hind host hhost
  refine ⟨N,hind,hgap,?_⟩
  intro keep hmeas hcoins hp
  exact recovery_above_threshold J htwo N keep hmeas hcoins p hp hp1 k W b L
    hchoice (fun h => hW (choice h)) hL hcap hmean u hu hb

end SplitGapIV
