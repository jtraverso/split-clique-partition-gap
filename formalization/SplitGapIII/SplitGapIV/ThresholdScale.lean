module

public import SplitGapIV.HostSampling

@[expose] public section

namespace SplitGapIV

open Finset MeasureTheory ProbabilityTheory GapExtremal QuadraticExteriorPalomar
open scoped ENNReal

variable {T V H Ω : Type*} [MeasurableSpace T] [Fintype H] [DecidableEq H]
variable [Fintype V] [DecidableEq V] [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Logarithmic upper threshold from a fractional palette cover of reciprocal cost η.
All physical host neighborhoods are chosen before the deletion law is applied. -/
theorem logarithmic_exact_gap_recovery
    (G : SimpleGraph V) [DecidableRel G.Adj] (ν : Measure T) [IsProbabilityMeasure ν]
    (P : T → Finset V) (hI : ∀ t, ∀ a ∈ P t, ∀ b ∈ P t, ¬ G.Adj a b)
    (hm : ∀ e ∈ jPairs G univ, MeasurableSet {t | e ⊆ P t})
    (η : ℝ) (hη0 : 0 ≤ η) (hη : ∀ e ∈ jPairs G univ, η ≤ ν.real {t | e ⊆ P t})
    (p : ℝ≥0∞) (hp1 : p.toReal ≤ 1) (n W : ℕ) (hn : 2 ≤ n)
    (hHn : Fintype.card H ≤ n) (hJn : (jPairs G univ).card ≤ n^2)
    (hSupply : 262144 * Real.log n ≤ p.toReal^2 * (η*Fintype.card H))
    (hW : ∀ t, (P t).card ≤ W)
    (hWidth : (W : ℝ) ≤ p.toReal * (η*Fintype.card H)/262144) :
    ∃ N : H → Finset V, (∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ G.Adj a b) ∧
      gap (hostGraph N) = residualSup G - residualInt G ∧
      ∀ keep : H × V → Set Ω, (∀ r, MeasurableSet (keep r)) →
        iIndepSet keep μ → (∀ r, μ (keep r) = p) →
        μ.real (recovery (jPairs G univ) N keep)ᶜ ≤
          2*Real.exp (-8*Real.log n) := by
  let x : ℝ := η*Fintype.card H
  let y : ℝ := Real.log n
  let s : ℝ := p.toReal^2*x
  let k : ℕ := ⌊x/4⌋₊
  let b : ℕ := ⌈2*p.toReal*W+10*y⌉₊
  let L : ℕ := 24*b
  have hnr : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hnp : 0 < (n:ℝ) := by linarith
  have hy : 1/2 ≤ y := by
    refine (show (1:ℝ)/2 ≤ Real.log 2 by linarith [Real.log_two_gt_d9]).trans ?_
    exact Real.log_le_log (by norm_num) hnr
  have hy0 : 0 ≤ y := by linarith
  have hx : 0 ≤ x := mul_nonneg hη0 (by positivity)
  have hp0 : 0 ≤ p.toReal := ENNReal.toReal_nonneg
  have hp2 : p.toReal^2 ≤ 1 := by nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hp1)]
  have hsx : s ≤ x := by
    exact mul_le_of_le_one_left hx hp2
  have hS : 262144*y ≤ s := hSupply
  have hk : (k : ℝ) ≤ x/4 := Nat.floor_le (by positivity)
  have hk' : x/4 < (k : ℝ)+1 := Nat.lt_floor_add_one _
  have hb : 2*p.toReal*W+10*y ≤ b := Nat.le_ceil _
  have hb' : (b : ℝ) < 2*p.toReal*W+10*y+1 := Nat.ceil_lt_add_one (by positivity)
  have hbpos : 0 < b := by
    have h := mul_nonneg (mul_nonneg (show (0:ℝ) ≤ 2 by norm_num) hp0) (show (0:ℝ) ≤ W by positivity)
    exact_mod_cast (show 0 < (b : ℝ) by linarith)
  have hL : 0 < L := Nat.mul_pos (by decide) hbpos
  have hmean : (L : ℝ) ≤ p.toReal^2*k/4 := by
    have h₁ := mul_le_mul_of_nonneg_left hk'.le (sq_nonneg p.toReal)
    have h₂ := mul_le_mul_of_nonneg_left hWidth hp0
    change p.toReal * (W : ℝ) ≤ p.toReal * (p.toReal*x/262144) at h₂
    have h₃ : p.toReal*(W:ℝ) ≤ s/262144 := by dsimp [s]; nlinarith
    have h₄ : s/4 ≤ p.toReal^2*(k : ℝ)+1 := by dsimp [s]; nlinarith
    change ((24*b:ℕ):ℝ) ≤ _
    push_cast
    linarith
  have hu : 10*y ≤ p.toReal^2*k/4 := by
    have h₁ := mul_le_mul_of_nonneg_left hk'.le (sq_nonneg p.toReal)
    have h₂ : s/4 ≤ p.toReal^2*(k : ℝ)+1 := by dsimp [s]; nlinarith
    linarith
  have hJ : ((jPairs G univ).card : ℝ) ≤ Real.exp (2*y) := by
    have hJ' : ((jPairs G univ).card : ℝ) ≤ (n:ℝ)^2 := by exact_mod_cast hJn
    rw [show 2*y = (2:ℕ)*y by norm_num, Real.exp_nat_mul, show Real.exp y = n from Real.exp_log hnp]
    exact hJ'
  have hH : (Fintype.card H : ℝ) ≤ Real.exp (2*y) := by
    apply (show (Fintype.card H : ℝ) ≤ (n:ℝ) by exact_mod_cast hHn).trans
    rw [show 2*y = (2:ℕ)*y by norm_num, Real.exp_nat_mul, show Real.exp y = n from Real.exp_log hnp]
    nlinarith
  have hbudget : ((jPairs G univ).card : ℝ)*Real.exp (-x/4) < 1 := by
    calc
      _ ≤ Real.exp (2*y) * Real.exp (-x/4) := mul_le_mul_of_nonneg_right hJ (by positivity)
      _ < _ := by
        rw [← Real.exp_add, ← Real.exp_zero]
        exact Real.exp_lt_exp.mpr (by linarith)
  obtain ⟨N,hind,hN,hr⟩ := exists_exact_gap_recovery_at_supply (H := H) (μ := μ) G ν P hI hm η hη
    p hp1 k W b L hk (by simpa [x, neg_mul] using hbudget)
    hW hL le_rfl hmean (10*y) (by linarith) hu (by linarith)
  refine ⟨N,hind,hN,fun keep hme hcoin hp => (hr keep hme hcoin hp).trans ?_⟩
  calc
    _ ≤ (Real.exp (2*y)+Real.exp (2*y))*Real.exp (-(10*y)) :=
      mul_le_mul_of_nonneg_right (add_le_add hJ hH) (by positivity)
    _ = _ := by
      rw [show Real.exp (2*y)+Real.exp (2*y) = 2*Real.exp (2*y) by ring,
        mul_assoc, ← Real.exp_add]
      congr 2
      ring

end SplitGapIV
