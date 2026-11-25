module

public import SplitGapIV.IndexBlocks
public import SplitGapIV.ResidualBound
public import R434.PackingTriangles

@[expose] public section

namespace SplitGapIV

open Finset GapExtremal GapExtremal.R434 GapExtremal.R434.H54 QuadraticExteriorPalomar
open scoped BigOperators

variable {A : Type} [Fintype A] [DecidableEq A]

omit [Fintype A] [DecidableEq A] in
private theorem indexed_color_ne {x y : IndexedCore A} (h : (indexedResidual A).Adj x y) :
    x.1.1 ≠ y.1.1 := by
  rcases h.1 with h | h
  · exact ne_of_lt h.1
  · exact ne_of_gt h.1

private theorem indexed_triangle_subset (o : BlockIndex A) {t : Triangle} (ht : t ∈ triangles) :
    triangleEdges (indexedBlockTriangle o t) ⊆ (indexedResidual A).edgeFinset := by
  intro e he
  rw [indexed_block_triangle_edges] at he
  obtain ⟨i,_,rfl⟩ := mem_image.mp he
  apply (indexed_block_edge_mem o _).mpr
  have h := (mem_filter.mp ht).2
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2

omit [Fintype A] in
private theorem indexed_triangle_card (o : BlockIndex A) (t : Triangle) :
    (triangleVertices (indexedBlockTriangle o t)).card = 3 := by
  let x := blockVertex o (0,t.1)
  let y := blockVertex o (1,t.2.1)
  let z := blockVertex o (2,t.2.2)
  have hxy : x ≠ y := fun h => (by decide : (0 : Fin 3) ≠ 1)
    (congrArg (fun q : IndexedCore A => q.1.1) h)
  have hxz : x ≠ z := fun h => (by decide : (0 : Fin 3) ≠ 2)
    (congrArg (fun q : IndexedCore A => q.1.1) h)
  have hyz : y ≠ z := fun h => (by decide : (1 : Fin 3) ≠ 2)
    (congrArg (fun q : IndexedCore A => q.1.1) h)
  change ({x,y,z} : Finset (IndexedCore A)).card = 3
  rw [card_insert_of_notMem (by simp [hxy,hxz]),card_pair hyz]

private theorem indexed_triangle_score (o : BlockIndex A) {t : Triangle} (ht : t ∈ triangles) :
    w (indexedResidual A) (triangleVertices (indexedBlockTriangle o t)) = 2 := by
  let T := indexedBlockTriangle o t
  let Q := triangleVertices T
  let B := indexedResidual A
  have hE : (inducedOn B Q).edgeFinset = triangleEdges T := by
    ext f
    induction f using Sym2.inductionOn with
    | _ a b =>
      constructor
      · intro hf
        have hp : B.Adj a b ∧ a ∈ Q ∧ b ∈ Q := SimpleGraph.mem_edgeFinset.mp hf
        exact (pair_mem_triangleVertices hp.1.ne).mp hp.2
      · intro hf
        have hAdj : B.Adj a b := SimpleGraph.mem_edgeFinset.mp (indexed_triangle_subset o ht hf)
        obtain ⟨ha,hb⟩ := (pair_mem_triangleVertices hAdj.ne).mpr hf
        exact SimpleGraph.mem_edgeFinset.mpr ⟨hAdj,ha,hb⟩
  have hinj : Function.Injective (fun k => indexedBlockEdge o (onTriangleIndex t k)) := by
    intro i j he
    have heq : ((o,onTriangleIndex t i) : BlockIndex A × Edge) = (o,onTriangleIndex t j) :=
      indexed_block_edge_injective he
    simpa only [onTriangleIndex_kind] using congrArg (fun q : BlockIndex A × Edge => q.2.1) heq
  have he : e B Q = 3 := by
    unfold e
    rw [hE,indexed_block_triangle_edges,card_image_of_injective _ hinj]
    simp
  change w B Q = 2
  rw [w,he,indexed_triangle_card]
  decide

private theorem indexed_fractional_witness :
    ∃ y : Finset (IndexedCore A) → ℝ, ResPack y ∧
      (∑ Q, y Q * (w (indexedResidual A) Q : ℝ)) = 36 * (Fintype.card A : ℝ)^3 := by
  classical
  let D := (univ : Finset (BlockIndex A)) ×ˢ support
  let Q (k : BlockIndex A × Triangle) := triangleVertices (indexedBlockTriangle k.1 k.2)
  let y (S : Finset (IndexedCore A)) : ℝ := ∑ k ∈ D, if Q k = S then (1:ℝ)/2 else 0
  have ht (k : BlockIndex A × Triangle) (hk : k ∈ D) : k.2 ∈ triangles :=
    support_valid (mem_product.mp hk).2
  refine ⟨y, ⟨?_,?_,?_⟩, ?_⟩
  · intro S
    exact sum_nonneg fun k _ => by split <;> norm_num
  · intro S hs
    by_contra! hsmall
    apply hs
    apply sum_eq_zero
    intro k _
    have hcard : (Q k).card = 3 := indexed_triangle_card _ _
    have hne : Q k ≠ S := fun he => by rw [he] at hcard; omega
    simp [hne]
  · intro a b hab
    have hsum : ∑ S, (if a ∈ S ∧ b ∈ S then y S else 0) =
        ∑ k ∈ D, (if s(a,b) ∈ triangleEdges (indexedBlockTriangle k.1 k.2) then (1:ℝ)/2 else 0) := by
      simp only [y,ite_sum_zero]
      rw [sum_comm]
      apply sum_congr rfl
      intro k _
      change (∑ S, (if a ∈ S ∧ b ∈ S then if Q k = S then (1:ℝ)/2 else 0 else 0)) =
        if s(a,b) ∈ triangleEdges (indexedBlockTriangle k.1 k.2) then (1:ℝ)/2 else 0
      rw [sum_eq_single (Q k)]
      · exact if_congr (pair_mem_triangleVertices hab) (by simp) rfl
      · intro S _ hne
        simp [hne.symm]
      · simp
    rw [hsum]
    by_cases hB : s(a,b) ∈ (indexedResidual A).edgeFinset
    · rw [indexed_edge_finset] at hB
      obtain ⟨⟨o,f⟩,hf,heq⟩ := mem_image.mp hB
      have hfilter :
          (D.filter fun k => s(a,b) ∈ triangleEdges (indexedBlockTriangle k.1 k.2)) =
            {o} ×ˢ support.filter (onEdge · f) := by
        ext k
        simp only [← heq,mem_filter,mem_product,mem_singleton,D,mem_univ,true_and,
          indexed_edge_triangle_iff]
        constructor
        · rintro ⟨hS,he,hon⟩
          exact ⟨he.symm,hS,hon⟩
        · rintro ⟨he,hS,hon⟩
          exact ⟨hS,he.symm,hon⟩
      rw [← sum_filter (s := D)
        (fun k => s(a,b) ∈ triangleEdges (indexedBlockTriangle k.1 k.2)) (fun _ => (1:ℝ)/2),
        hfilter]
      simp only [sum_const,nsmul_eq_mul,card_product,card_singleton,twice_on_each_edge f (mem_product.mp hf).2]
      norm_num
    · have hzero : ∑ k ∈ D, (if s(a,b) ∈ triangleEdges (indexedBlockTriangle k.1 k.2)
          then (1:ℝ)/2 else 0) = 0 := by
        apply sum_eq_zero
        intro k hk
        have hne : s(a,b) ∉ triangleEdges (indexedBlockTriangle k.1 k.2) :=
          fun he => hB (indexed_triangle_subset _ (ht k hk) he)
        simp [hne]
      rw [hzero]
      norm_num
  · simp only [y,sum_mul,ite_mul,zero_mul]
    rw [sum_comm]
    have hval : ∑ k ∈ D, ∑ S, (if Q k = S then (1:ℝ)/2 * (w (indexedResidual A) S : ℝ) else 0) =
        ∑ _k ∈ D, (1:ℝ) := by
      apply sum_congr rfl
      intro k hk
      have hw : w (indexedResidual A) (Q k) = 2 := indexed_triangle_score _ (ht k hk)
      simp [hw]
    change ∑ k ∈ D, ∑ S, (if Q k = S then (1:ℝ)/2 * (w (indexedResidual A) S : ℝ) else 0) = _
    rw [hval]
    simp only [D,sum_const,nsmul_eq_mul,mul_one,card_product,card_univ,support_count,Nat.cast_mul,
      Fintype.card_prod,BlockIndex]
    ring

private theorem indexed_fractional_upper (y : Finset (IndexedCore A) → ℝ) (hy : ResPack y) :
    ∑ Q, y Q * (w (indexedResidual A) Q : ℝ) ≤ 36 * (Fintype.card A : ℝ)^3 := by
  classical
  let B := indexedResidual A
  let E := adjPairs B (univ : Finset (IndexedCore A))
  have hmass : ∑ Q, y Q * (e B Q : ℝ) ≤ (B.edgeFinset.card : ℝ) := by
    calc
      _ = ∑ p ∈ E, resLoad y p := by
        unfold resLoad
        rw [sum_comm]
        apply sum_congr rfl
        intro Q _
        have hf : E.filter (· ⊆ Q) = adjPairs B Q := by
          ext p
          simp only [E,adjPairs,mem_filter,mem_powersetCard,subset_univ,true_and]
          tauto
        rw [e_eq_card_adjPairs,← sum_filter,hf,sum_const,nsmul_eq_mul,mul_comm]
      _ ≤ ∑ _p ∈ E, (1:ℝ) := by
        apply sum_le_sum
        intro p hp
        obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp
          (mem_powersetCard.mp (mem_filter.mp hp).1).2
        exact (resLoad_pair y a b).trans_le (hy.load a b hab)
      _ = _ := by
        rw [sum_const,nsmul_eq_mul,mul_one,← e_eq_card_adjPairs B univ]
        have hE : (inducedOn B univ).edgeFinset = B.edgeFinset := by
          ext f
          induction f using Sym2.inductionOn with
          | _ a b =>
            rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeFinset]
            change (B.Adj a b ∧ a ∈ univ ∧ b ∈ univ) ↔ B.Adj a b
            simp
        rw [e,hE]
  calc
    _ ≤ ∑ Q, y Q * (2 * (e B Q:ℝ)/3) := by
      apply sum_le_sum
      intro Q _
      by_cases hy0 : y Q = 0
      · simp [hy0]
      · apply mul_le_mul_of_nonneg_left _ (hy.nonneg Q)
        have hcount := tripartite_edge_bound B (fun v => v.1.1)
          (fun _ _ h => indexed_color_ne h) Q
        have hs := (slack_of_tripartite_counts _ _ (hy.two Q hy0) hcount).1
        rw [← pieceSlack_formula B Q,pieceSlack] at hs
        linarith
    _ = 2/3 * ∑ Q, y Q * (e B Q : ℝ) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro Q _
      ring
    _ ≤ 2/3 * (B.edgeFinset.card : ℝ) := mul_le_mul_of_nonneg_left hmass (by norm_num)
    _ = _ := by
      change 2/3 * ((indexedResidual A).edgeFinset.card : ℝ) = _
      rw [indexed_edge_count]
      push_cast
      ring

theorem indexed_residual_fractional_value :
    residualSup (indexedResidual A) = 36 * (Fintype.card A : ℝ)^3 := by
  obtain ⟨y,hy,he⟩ := indexed_fractional_witness (A := A)
  unfold residualSup
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · exact ⟨_,y,hy,he⟩
  · rintro _ ⟨z,hz,rfl⟩
    exact indexed_fractional_upper z hz
  · intro z hz
    exact ⟨_,⟨y,hy,he⟩,hz⟩

/-- The integral obstruction survives all choices of clique pieces in the indexed residual. -/
theorem indexed_residual_gap_lower :
    2/9 * (Fintype.card A : ℝ)^3 ≤
      residualSup (indexedResidual A) - residualInt (indexedResidual A) := by
  classical
  let B := indexedResidual A
  let P := (exists_best_pack B).choose
  have hP : IsPack P := (exists_best_pack B).choose_spec.1
  obtain ⟨T,X,hT,hpack,hpart,_,hloss⟩ :=
    packing_to_triangles B (fun v => v.1.1) (fun _ _ h => indexed_color_ne h) hP
  let family (o : BlockIndex A) := (triangles.filter (fun t => indexedBlockTriangle o t ∈ T)).image
    (indexedBlockTriangle o)
  have hcap (o : BlockIndex A) : (family o).card ≤ 16 := by
    apply card_image_le.trans
    apply local_packing_le_sixteen _ (filter_subset _ _)
    intro i t ht t' ht' he
    change onTriangleIndex t i = onTriangleIndex t' i at he
    by_contra hn
    have hl : indexedBlockEdge o (onTriangleIndex t i) ∈ triangleEdges (indexedBlockTriangle o t) := by
      rw [indexed_block_triangle_edges]
      exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
    have hr : indexedBlockEdge o (onTriangleIndex t i) ∈ triangleEdges (indexedBlockTriangle o t') := by
      rw [he,indexed_block_triangle_edges]
      exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
    exact disjoint_left.mp (hpack (mem_filter.mp ht).2 (mem_filter.mp ht').2
      (fun hh => hn (indexed_block_triangle_injective o hh))) hl hr
  have hsub : T ⊆ (univ : Finset (BlockIndex A)).biUnion family := by
    intro t ht
    have hE : triangleEdges t ⊆ B.edgeFinset := by
      intro e he
      rw [← hpart]
      exact mem_union_right _ (mem_biUnion.mpr ⟨t,ht,he⟩)
    obtain ⟨o,k,hk,rfl⟩ := indexed_triangle_origin t (hT t ht) hE
    exact mem_biUnion.mpr ⟨o,mem_univ _,mem_image.mpr ⟨k,mem_filter.mpr ⟨hk,ht⟩,rfl⟩⟩
  have hTsize : T.card ≤ 16*(Fintype.card A)^3 := by
    apply (card_le_card hsub).trans
    have h := card_biUnion_le_card_mul (univ : Finset (BlockIndex A)) family 16 (fun o _ => hcap o)
    simp only [card_univ,BlockIndex,Fintype.card_prod] at h
    exact h.trans (by ring_nf; exact le_rfl)
  have htotal : B.edgeFinset.card ≤ X.card + 3*T.card := by
    rw [← hpart]
    have hcard : (T.biUnion triangleEdges).card ≤ 3 * T.card := by
      simpa only [mul_comm] using
        (card_biUnion_le_card_mul T triangleEdges 3 (fun t _ => triangleEdges_card_le t))
    exact (card_union_le _ _).trans (Nat.add_le_add_left hcard _)
  have hB : B.edgeFinset.card = 54*(Fintype.card A)^3 := indexed_edge_count
  have hX : 6*(Fintype.card A)^3 ≤ X.card := by rw [hB] at htotal; omega
  have hX' : 6*(Fintype.card A : ℝ)^3 ≤ X.card := by exact_mod_cast hX
  have hB' : (B.edgeFinset.card : ℝ) = 54*(Fintype.card A : ℝ)^3 := by exact_mod_cast hB
  have hscore : ∑ Q ∈ P, (w B Q : ℝ) = residualInt B := by
    simp [residualInt,P]
  rw [hB',hscore] at hloss
  rw [indexed_residual_fractional_value]
  change _ ≤ _ - (residualInt B : ℝ)
  linarith only [hX',hloss]

theorem indexed_residual_gap_upper :
    residualSup (indexedResidual A) - residualInt (indexedResidual A) ≤
      36 * (Fintype.card A : ℝ)^3 := by
  have h := (exists_best_pack (indexedResidual A)).choose_spec.2.2 ∅ (by simp [IsPack])
  have h0 : 0 ≤ (residualInt (indexedResidual A) : ℝ) := by
    exact_mod_cast (show 0 ≤ residualInt (indexedResidual A) from by simpa [residualInt] using h)
  rw [indexed_residual_fractional_value]
  linarith

end SplitGapIV
