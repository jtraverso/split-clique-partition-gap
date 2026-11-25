module

public import SplitGapIII.Reassignment

@[expose] public section

namespace SplitGapIV

open Finset GapExtremal QuadraticExteriorPalomar
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Every positive gap is bounded by twice the number of requests. -/
theorem residual_gap_le_requests (B : SimpleGraph V) [DecidableRel B.Adj]
    (hV : 2 ≤ Fintype.card V) :
    residualSup B - residualInt B ≤ 2 * ((jPairs B univ).card : ℝ) := by
  classical
  let K := (univ : Finset V).card.choose 2
  have hK : 0 < K := Nat.choose_pos (by simpa using hV)
  have hbound : residualSup B ≤ (K : ℝ) - 1 := by
    apply csSup_le
    · exact ⟨0, fun _ => 0, by constructor <;> simp, by simp⟩
    rintro _ ⟨y, hy, rfl⟩
    have hmass : ∑ Q, y Q * (Q.card.choose 2 : ℝ) ≤ K := by
      calc
        _ = ∑ p ∈ (univ : Finset V).powersetCard 2, resLoad y p := by
          unfold resLoad
          rw [sum_comm]
          apply sum_congr rfl
          intro Q _
          have hfilter : ((univ : Finset V).powersetCard 2).filter (· ⊆ Q) =
              Q.powersetCard 2 := by
            ext p
            simp [mem_powersetCard, and_comm]
          rw [← sum_filter, hfilter, sum_const, card_powersetCard, nsmul_eq_mul, mul_comm]
        _ ≤ ∑ _p ∈ (univ : Finset V).powersetCard 2, (1 : ℝ) := by
          apply sum_le_sum
          intro p hp
          obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp (mem_powersetCard.mp hp).2
          rw [resLoad_pair]
          exact hy.load a b hab
        _ = K := by simp [K]
    have hK' : 0 < (K : ℝ) := by exact_mod_cast hK
    have hscale : 0 ≤ ((K : ℝ) - 1) / K := by
      apply div_nonneg _ hK'.le
      exact sub_nonneg.mpr (by exact_mod_cast hK)
    calc
      _ ≤ ∑ Q, ((K : ℝ) - 1) / K * (y Q * (Q.card.choose 2 : ℝ)) := by
        apply sum_le_sum
        intro Q _
        rw [mul_left_comm]
        apply mul_le_mul_of_nonneg_left _ (hy.nonneg Q)
        have hQ : (Q.card.choose 2 : ℝ) ≤ K := by
          exact_mod_cast Nat.choose_le_choose 2 (card_le_card (subset_univ Q))
        have hw := w_add_two_j B Q
        have hw' : (w B Q : ℝ) + 2 * ((jPairs B Q).card : ℝ) =
            (Q.card.choose 2 : ℝ) - 1 := by exact_mod_cast hw
        apply le_trans (show (w B Q : ℝ) ≤ (Q.card.choose 2 : ℝ) - 1 by
          linarith [show 0 ≤ ((jPairs B Q).card : ℝ) by positivity])
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ hK').2
        nlinarith
      _ = ((K : ℝ) - 1) / K * ∑ Q, y Q * (Q.card.choose 2 : ℝ) := by rw [mul_sum]
      _ ≤ (K : ℝ) - 1 := by
        convert mul_le_mul_of_nonneg_left hmass hscale using 1
        field_simp
  have hi := (exists_best_pack B).choose_spec.2.2
    {univ} (by simp [IsPack])
  have hi' : (w B (univ : Finset V) : ℝ) ≤ residualInt B := by
    exact_mod_cast (show w B univ ≤ residualInt B from by simpa [residualInt] using hi)
  have hw : (w B (univ : Finset V) : ℝ) + 2 * ((jPairs B univ).card : ℝ) =
      (K : ℝ) - 1 := by exact_mod_cast w_add_two_j B (univ : Finset V)
  linarith

/-- Largest number of requests at a core vertex. -/
def requestDegree (J : Finset (Finset V)) : ℕ :=
  (univ : Finset V).sup fun v => (J.filter (v ∈ ·)).card

/-- A maximal disjoint family of pairs covers the request graph by endpoint stars. -/
theorem exists_request_matching (J : Finset (Finset V))
    (htwo : ∀ e ∈ J, e.card = 2) :
    ∃ M ⊆ J, (∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f) ∧
      J.card ≤ 2 * requestDegree J * M.card := by
  classical
  let A := J.powerset.filter fun M => ∀ e ∈ M, ∀ f ∈ M, e ≠ f → Disjoint e f
  have hA : A.Nonempty := ⟨∅, by simp [A]⟩
  obtain ⟨M, hM, hmax⟩ := exists_max_image A card hA
  obtain ⟨hsub, hdis⟩ := mem_filter.mp hM
  have hsub' := mem_powerset.mp hsub
  refine ⟨M, hsub', hdis, ?_⟩
  have hcover : J ⊆ (M.biUnion fun e => e.biUnion fun v => J.filter (v ∈ ·)) := by
    intro e he
    by_contra hn
    have hd : ∀ f ∈ M, Disjoint e f := by
      intro f hf
      rw [disjoint_left]
      intro v hv hv'
      exact hn (mem_biUnion.mpr ⟨f, hf, mem_biUnion.mpr ⟨v, hv', mem_filter.mpr ⟨he,hv⟩⟩⟩)
    have heM : e ∉ M := by
      intro hem
      have hz : e = ∅ := disjoint_self.mp (hd e hem)
      have ht := htwo e he
      simp [hz] at ht
    have hin : insert e M ∈ A := by
      refine mem_filter.mpr ⟨mem_powerset.mpr (insert_subset he hsub'), ?_⟩
      intro x hx y hy hxy
      rcases mem_insert.mp hx with hxe | hx'
      · subst x
        rcases mem_insert.mp hy with hye | hy'
        · subst y
          exact (hxy rfl).elim
        · exact hd y hy'
      · rcases mem_insert.mp hy with hye | hy'
        · subst y
          exact (hd x hx').symm
        · exact hdis x hx' y hy' hxy
    have hle := hmax _ hin
    simp [heM] at hle
  calc
    J.card ≤ _ := card_le_card hcover
    _ ≤ ∑ e ∈ M, (e.biUnion fun v => J.filter (v ∈ ·)).card := card_biUnion_le
    _ ≤ ∑ e ∈ M, 2 * requestDegree J := by
      apply sum_le_sum
      intro e he
      calc
        _ ≤ ∑ v ∈ e, (J.filter (v ∈ ·)).card := card_biUnion_le
        _ ≤ ∑ _v ∈ e, requestDegree J := by
          apply sum_le_sum
          intro v _
          exact le_sup (f := fun v => (J.filter (v ∈ ·)).card) (mem_univ v)
        _ = _ := by simp [htwo e (hsub' he)]
    _ = _ := by simp [mul_comm]

end SplitGapIV
