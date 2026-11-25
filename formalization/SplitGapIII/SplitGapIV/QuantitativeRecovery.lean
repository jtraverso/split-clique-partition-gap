module

public import SplitGapIV.IndexGap
public import SplitGapIV.IndexRecovery

@[expose] public section

namespace SplitGapIV

open Finset MeasureTheory ProbabilityTheory GapExtremal
open scoped ENNReal

/-- The same fixed split graph has a quantitative gap and admits full physical
recovery, with exact preservation of that gap, above the logarithmic threshold. -/
theorem indexed_quantitative_physical_recovery
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ) (hn : 2 ≤ n) (hlog : 120 ≤ Real.log n) (p : ℝ≥0∞) (hp : p.toReal ≤ 1)
    (hsupply : 471859200 * Real.log n ≤ p.toReal^2 * (n : ℝ)) :
    ∃ s : ℕ, ∃ N : IndexedHosts (Fin s) n → Finset (IndexedCore (Fin s)),
      Fintype.card (IndexedCore (Fin s) ⊕ IndexedHosts (Fin s) n) = n ∧
      (∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ (indexedResidual (Fin s)).Adj a b) ∧
      2/9 * (s : ℝ)^3 ≤ gap (hostGraph N) ∧
      (4/81 : ℝ) * (p.toReal * (n : ℝ) / 56623104000)^3 ≤ (gap (hostGraph N))^2 ∧
      ∀ keep : IndexedHosts (Fin s) n × IndexedCore (Fin s) → Set Ω,
        (∀ r, MeasurableSet (keep r)) → iIndepSet keep μ → (∀ r, μ (keep r) = p) →
        μ.real {ω | ¬ (ω ∈ recovery (jPairs (indexedResidual (Fin s)) univ) N keep ∧
          gap (hostGraph (live N keep ω)) = gap (hostGraph N))} ≤
          2 * Real.exp (-8 * Real.log n) := by
  obtain ⟨s,N,hcore,hcard,hind,hgap,hrec⟩ :=
    indexed_witness_all_large_orders (μ := μ) n hn hlog p hp hsupply
  have hs : (2 : ℝ)/9 * (s : ℝ)^3 ≤ gap (hostGraph N) := by
    rw [hgap]
    simpa only [Fintype.card_fin] using (indexed_residual_gap_lower (A := Fin s))
  have hcore' : p.toReal * (n : ℝ) / 56623104000 ≤ (s : ℝ)^2 := by
    rw [indexed_core_card,Fintype.card_fin] at hcore
    push_cast at hcore
    linarith
  have hscale := pow_le_pow_left₀ (show 0 ≤ p.toReal*(n : ℝ)/56623104000 by positivity) hcore' 3
  have hsq := pow_le_pow_left₀ (show 0 ≤ (2:ℝ)/9*(s:ℝ)^3 by positivity) hs 2
  refine ⟨s,N,hcard,hind,hs,?_,?_⟩
  · calc
      _ ≤ (4/81 : ℝ) * ((s : ℝ)^2)^3 := mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ = ((2:ℝ)/9*(s:ℝ)^3)^2 := by ring
      _ ≤ _ := hsq
  · intro keep hme hcoins hprob
    refine (measureReal_mono ?_ (measure_ne_top μ _)).trans (hrec keep hme hcoins hprob)
    intro ω hbad hgood
    exact hbad ⟨hgood,(recovery_preserves_gap _ N keep ω hind hgood).trans hgap.symm⟩

end SplitGapIV
