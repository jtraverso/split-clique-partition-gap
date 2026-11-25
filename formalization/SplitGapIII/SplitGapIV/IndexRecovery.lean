module

public import SplitGapIV.IndexGrid
public import SplitGapIV.ThresholdScale

@[expose] public section

namespace SplitGapIV

open Finset MeasureTheory ProbabilityTheory GapExtremal QuadraticExteriorPalomar
open scoped ENNReal

variable {A Ω : Type*} [Fintype A] [DecidableEq A] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [DecidableEq A] in
theorem indexed_core_card : Fintype.card (IndexedCore A) = 15*(Fintype.card A)^2 := by
  simp [IndexedCore, GapExtremal.R434.H54.Role, pow_two]

abbrev IndexedHosts (A : Type*) [Fintype A] (n : ℕ) :=
  Fin (n - Fintype.card (IndexedCore A))

/-- At the logarithmic deletion threshold the actual indexed residual has independent
palettes of total order n and recovers its exact residual gap with polynomial error. -/
theorem indexed_witness_at_log_threshold
    (n : ℕ) (hn : 2 ≤ n) (p : ℝ≥0∞) (hp1 : p.toReal ≤ 1)
    (hsupply : 471859200 * Real.log n ≤ p.toReal^2 * (n : ℝ))
    (hwidth : (Fintype.card (IndexedCore A) : ℝ) ≤ p.toReal * n / 471859200) :
    ∃ N : IndexedHosts A n → Finset (IndexedCore A),
      Fintype.card (IndexedCore A ⊕ IndexedHosts A n) = n ∧
      (∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ (indexedResidual A).Adj a b) ∧
      gap (hostGraph N) = residualSup (indexedResidual A) - residualInt (indexedResidual A) ∧
      ∀ keep : IndexedHosts A n × IndexedCore A → Set Ω,
        (∀ r, MeasurableSet (keep r)) → iIndepSet keep μ → (∀ r, μ (keep r) = p) →
        μ.real (recovery (jPairs (indexedResidual A) univ) N keep)ᶜ ≤
          2*Real.exp (-8*Real.log n) := by
  classical
  let v := Fintype.card (IndexedCore A)
  let H := IndexedHosts A n
  have hp0 : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have hv : 2*(v : ℝ) ≤ n := by
    have hpn : p.toReal*(n:ℝ) ≤ n := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hp1) (Nat.cast_nonneg (α := ℝ) n)]
    change (v : ℝ) ≤ p.toReal*n/471859200 at hwidth
    linarith
  have hvn : v ≤ n := by exact_mod_cast (show (v : ℝ) ≤ n by linarith)
  have hhn : Fintype.card H ≤ n := by simp [H, IndexedHosts]
  have hh : (n : ℝ) ≤ 2*(Fintype.card H : ℝ) := by
    have hv' : 2*v ≤ n := by exact_mod_cast hv
    have hh' : n ≤ 2*Fintype.card H := by
      simp only [H, IndexedHosts, Fintype.card_fin]
      change n ≤ 2*(n-v)
      omega
    exact_mod_cast hh'
  let B := indexedResidual A
  have hj : (jPairs B univ).card ≤ n^2 := by
    calc
      _ ≤ ((univ : Finset (IndexedCore A)).powersetCard 2).card := card_filter_le _ _
      _ = v.choose 2 := by simp [v]
      _ ≤ v^2 := Nat.choose_le_pow _ _
      _ ≤ n^2 := Nat.pow_le_pow_left hvn _
  have hcoverage (e : Finset (IndexedCore A)) (he : e ∈ jPairs B univ) :
      (1:ℝ)/900 ≤ indexedTemplateMeasure.real {t | e ⊆ indexedPalette t} := by
    obtain ⟨x,y,_,rfl⟩ := card_eq_two.mp (two_of_mem_jPairs he)
    exact indexed_palette_coverage (nonadj_of_mem_jPairs he x (by simp) y (by simp))
  obtain ⟨N,hind,hN,hr⟩ := logarithmic_exact_gap_recovery (H := H) (μ := μ) B
    indexedTemplateMeasure indexedPalette (fun t a ha b hb => indexed_palette_independent t a b ha hb)
    (fun _ _ => (Set.toFinite _).measurableSet) (1/900) (by norm_num) hcoverage p hp1
    n v hn hhn hj (by
      have h₂ := mul_le_mul_of_nonneg_left hh (sq_nonneg p.toReal)
      linarith) (fun t => card_le_univ _) (by
      have h₂ := mul_le_mul_of_nonneg_left hh hp0
      change (v : ℝ) ≤ p.toReal * n / 471859200 at hwidth
      linarith)
  refine ⟨N,?_,hind,hN,hr⟩
  simp only [Fintype.card_sum,H,IndexedHosts,Fintype.card_fin]
  change v+(n-v) = n
  omega

/-- At every sufficiently large order, choose the number of indices so that the actual
core has order proportional to pn, while satisfying the upper threshold budget. -/
theorem indexed_witness_all_large_orders
    (n : ℕ) (hn : 2 ≤ n) (hlog : 120 ≤ Real.log n) (p : ℝ≥0∞) (hp1 : p.toReal ≤ 1)
    (hsupply : 471859200 * Real.log n ≤ p.toReal^2 * (n : ℝ)) :
    ∃ s : ℕ, ∃ N : IndexedHosts (Fin s) n → Finset (IndexedCore (Fin s)),
      p.toReal*(n : ℝ)/3774873600 ≤ Fintype.card (IndexedCore (Fin s)) ∧
      Fintype.card (IndexedCore (Fin s) ⊕ IndexedHosts (Fin s) n) = n ∧
      (∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ (indexedResidual (Fin s)).Adj a b) ∧
      gap (hostGraph N) = residualSup (indexedResidual (Fin s)) - residualInt (indexedResidual (Fin s)) ∧
      ∀ keep : IndexedHosts (Fin s) n × IndexedCore (Fin s) → Set Ω,
        (∀ r, MeasurableSet (keep r)) → iIndepSet keep μ → (∀ r, μ (keep r) = p) →
        μ.real (recovery (jPairs (indexedResidual (Fin s)) univ) N keep)ᶜ ≤
          2*Real.exp (-8*Real.log n) := by
  let x := p.toReal*(n:ℝ)/471859200
  let W : ℕ := ⌊x⌋₊
  let M := W/15
  let s := Nat.sqrt M
  have hpn : p.toReal^2*(n:ℝ) ≤ p.toReal*n := by
    nlinarith [mul_nonneg (mul_nonneg (ENNReal.toReal_nonneg (a := p)) (sub_nonneg.mpr hp1))
      (Nat.cast_nonneg (α := ℝ) n)]
  have hx : 120 ≤ x := by dsimp [x]; linarith
  have hW : (W : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hW' : x < (W : ℝ)+1 := Nat.lt_floor_add_one _
  have hWdiv : 15*M ≤ W := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self W 15
  have hWdiv' : W < 15*(M+1) := by
    dsimp [M]
    omega
  have hs : s^2 ≤ M := by rw [pow_two]; exact Nat.sqrt_le M
  have hs' : M < (s+1)^2 := by rw [pow_two]; exact Nat.lt_succ_sqrt M
  have hspos : 0 < s := by
    by_contra! hh
    have heq : s=0 := Nat.eq_zero_of_le_zero hh
    rw [heq] at hs'
    have hm : M=0 := by omega
    rw [hm] at hWdiv'
    have hWr : (W:ℝ) < 15 := by exact_mod_cast (show W<15 by simpa using hWdiv')
    linarith
  have hms : M < 4*s^2 := by
    have hs₁ : 1 ≤ s := hspos
    refine hs'.trans_le ?_
    have hmul := Nat.mul_le_mul (show s+1 ≤ 2*s by omega) (show s+1 ≤ 2*s by omega)
    nlinarith
  have hc : Fintype.card (IndexedCore (Fin s)) = 15*s^2 := by
    rw [indexed_core_card,Fintype.card_fin]
  have hcoreU : (Fintype.card (IndexedCore (Fin s)) : ℝ) ≤ x := by
    rw [hc]
    exact (show ((15*s^2:ℕ):ℝ) ≤ W by exact_mod_cast
      (Nat.mul_le_mul_left 15 hs).trans hWdiv).trans hW
  have hcoreL : x/8 ≤ Fintype.card (IndexedCore (Fin s)) := by
    rw [hc]
    have hWr : (W:ℝ) < 15*((M:ℝ)+1) := by exact_mod_cast hWdiv'
    have hMr : (M:ℝ) < 4*(s:ℝ)^2 := by exact_mod_cast hms
    push_cast
    linarith
  obtain ⟨N,hcard,hind,hgap,hr⟩ :=
    indexed_witness_at_log_threshold (A := Fin s) (μ := μ) n hn p hp1 hsupply hcoreU
  refine ⟨s,N,?_,hcard,hind,hgap,hr⟩
  convert hcoreL using 1
  dsimp [x]
  ring

end SplitGapIV
