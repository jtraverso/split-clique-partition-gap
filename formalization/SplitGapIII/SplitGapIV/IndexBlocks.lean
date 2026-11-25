module

public import SplitGapIV.IndexGrid
public import R434.CoreFractional

@[expose] public section

namespace SplitGapIV

open Finset GapExtremal.R434 GapExtremal.R434.H54

variable {A : Type} [DecidableEq A]

abbrev BlockIndex (A : Type) := A × A × A

def blockVertex (o : BlockIndex A) (r : Role) : IndexedCore A :=
  (r, if r.1 = 0 then (o.1, o.2.1) else if r.1 = 1 then (o.1, o.2.2) else (o.2.1, o.2.2))

def indexedBlockEdge (o : BlockIndex A) (e : Edge) : Sym2 (IndexedCore A) :=
  s(blockVertex o (lowerPart e.1,e.2.1), blockVertex o (upperPart e.1,e.2.2))

def indexedBlockTriangle (o : BlockIndex A) (t : Triangle) : OrderedTriangle (IndexedCore A) :=
  (blockVertex o (0,t.1),blockVertex o (1,t.2.1),blockVertex o (2,t.2.2))

theorem indexed_block_edge_injective :
    Function.Injective (fun z : BlockIndex A × Edge => indexedBlockEdge z.1 z.2) := by
  intro ⟨o,⟨i,a,b⟩⟩ ⟨p,⟨j,c,d⟩⟩ he
  change s(blockVertex o (lowerPart i,a), blockVertex o (upperPart i,b)) =
    s(blockVertex p (lowerPart j,c), blockVertex p (upperPart j,d)) at he
  rcases Sym2.eq_iff.mp he with ⟨hl,hr⟩ | ⟨hl,hr⟩
  · have hrl := congrArg (fun x : IndexedCore A => x.1) hl
    have hrr := congrArg (fun x : IndexedCore A => x.1) hr
    have hi : i = j := by
      change ((lowerPart i,a) : Role) = (lowerPart j,c) at hrl
      change ((upperPart i,b) : Role) = (upperPart j,d) at hrr
      have h1 : lowerPart i = lowerPart j := congrArg Prod.fst hrl
      have h2 : upperPart i = upperPart j := congrArg Prod.fst hrr
      calc
        i = edgeKind (lowerPart i) (upperPart i) := (kind_of_parts i).symm
        _ = edgeKind (lowerPart j) (upperPart j) := by rw [h1,h2]
        _ = j := kind_of_parts j
    have ha : a = c := congrArg Prod.snd hrl
    have hb : b = d := congrArg Prod.snd hrr
    subst j
    subst c
    subst d
    have h₁ := congrArg (fun x : IndexedCore A => x.2) hl
    have h₂ := congrArg (fun x : IndexedCore A => x.2) hr
    have hp : o = p := by
      fin_cases i <;> simp [blockVertex, lowerPart, upperPart, Prod.mk.injEq] at h₁ h₂ <;>
        exact Prod.ext (by tauto) (Prod.ext (by tauto) (by tauto))
    subst p
    rfl
  · have h₁ : lowerPart i = upperPart j := congrArg (fun x : IndexedCore A => x.1.1) hl
    have h₂ : upperPart i = lowerPart j := congrArg (fun x : IndexedCore A => x.1.1) hr
    have hi := part_lt i
    rw [h₁,h₂] at hi
    exact (not_lt_of_ge (part_lt j).le hi).elim

variable [Fintype A]

theorem indexed_block_edge_mem (o : BlockIndex A) (e : Edge) :
    indexedBlockEdge o e ∈ (indexedResidual A).edgeFinset ↔ e ∈ edges := by
  rcases e with ⟨i,a,b⟩
  rw [indexedBlockEdge,SimpleGraph.mem_edgeFinset]
  change roleGraph.Adj (lowerPart i,a) (upperPart i,b) ∧
    sharedKey (blockVertex o (lowerPart i,a)) (upperPart i) =
      sharedKey (blockVertex o (upperPart i,b)) (lowerPart i) ↔ _
  rw [roleGraph_ordered (part_lt i),kind_of_parts]
  have h : sharedKey (blockVertex o (lowerPart i,a)) (upperPart i) =
      sharedKey (blockVertex o (upperPart i,b)) (lowerPart i) := by
    fin_cases i <;> simp [sharedKey,blockVertex,lowerPart,upperPart]
  simp [h]

theorem indexed_edge_finset :
    (indexedResidual A).edgeFinset =
      ((univ : Finset (BlockIndex A)) ×ˢ edges).image
        (fun z => indexedBlockEdge z.1 z.2) := by
  classical
  ext q
  induction q using Sym2.inductionOn with
  | _ x y =>
    constructor
    · intro h
      have had := SimpleGraph.mem_edgeFinset.mp h
      have hentry : ∀ x y : IndexedCore A, x.1.1 < y.1.1 →
          (indexedResidual A).Adj x y →
          s(x,y) ∈ ((univ : Finset (BlockIndex A)) ×ˢ edges).image
            (fun z => indexedBlockEdge z.1 z.2) := by
        rintro ⟨⟨i,r⟩,a,b⟩ ⟨⟨j,s⟩,c,d⟩ hlt ha
        have he : (edgeKind i j,r,s) ∈ edges := (roleGraph_ordered hlt).mp ha.1
        have hkey := ha.2
        fin_cases i <;> fin_cases j <;> norm_num at hlt
        · have h' : a = c := by simpa [sharedKey] using hkey
          subst c
          exact mem_image.mpr ⟨((a,b,d),(0,r,s)),mem_product.mpr ⟨mem_univ _,he⟩,rfl⟩
        · have h' : b = c := by simpa [sharedKey] using hkey
          subst c
          exact mem_image.mpr ⟨((a,b,d),(2,r,s)),mem_product.mpr ⟨mem_univ _,he⟩,rfl⟩
        · have h' : b = d := by simpa [sharedKey] using hkey
          subst d
          exact mem_image.mpr ⟨((a,c,b),(1,r,s)),mem_product.mpr ⟨mem_univ _,he⟩,rfl⟩
      rcases had.1 with hxy | hyx
      · exact hentry x y hxy.1 had
      · rw [Sym2.eq_swap]
        exact hentry y x hyx.1 had.symm
    · rintro he
      obtain ⟨⟨o,e⟩,hp,heq⟩ := mem_image.mp he
      rw [← heq]
      exact (indexed_block_edge_mem o e).mpr (mem_product.mp hp).2

theorem indexed_edge_count :
    (indexedResidual A).edgeFinset.card = 54 * (Fintype.card A)^3 := by
  rw [indexed_edge_finset,card_image_of_injective _ indexed_block_edge_injective,
    card_product,card_univ,edge_count]
  simp [BlockIndex,Fintype.card_prod]
  ring

omit [Fintype A] in
theorem indexed_block_triangle_edges (o : BlockIndex A) (t : Triangle) :
    triangleEdges (indexedBlockTriangle o t) =
      univ.image (fun k => indexedBlockEdge o (onTriangleIndex t k)) := by
  ext f
  simp only [triangleEdges,mem_insert,mem_singleton,mem_image,mem_univ,true_and]
  constructor
  · rintro (hh | hh | hh)
    · exact ⟨0,hh.symm⟩
    · exact ⟨1,hh.symm⟩
    · exact ⟨2,hh.symm⟩
  · rintro ⟨k,hk⟩
    fin_cases k
    · exact Or.inl hk.symm
    · exact Or.inr (Or.inl hk.symm)
    · exact Or.inr (Or.inr hk.symm)

theorem indexed_edge_triangle_iff (o p : BlockIndex A) (t : Triangle) (e : Edge) :
    indexedBlockEdge p e ∈ triangleEdges (indexedBlockTriangle o t) ↔ p=o ∧ onEdge t e := by
  rw [indexed_block_triangle_edges]
  constructor
  · intro he
    obtain ⟨i,_,hi⟩ := mem_image.mp he
    have hh : ((o,onTriangleIndex t i) : BlockIndex A × Edge) = (p,e) :=
      indexed_block_edge_injective hi
    have hp : o = p := congrArg Prod.fst hh
    have ht : onTriangleIndex t i = e := congrArg Prod.snd hh
    have hi' : i = e.1 := (onTriangleIndex_kind t i).symm.trans (congrArg Prod.fst ht)
    exact ⟨hp.symm, (onEdge_iff_index t e).mpr (hi' ▸ ht.symm)⟩
  · rintro ⟨rfl,h⟩
    exact mem_image.mpr ⟨e.1,mem_univ _,congrArg (indexedBlockEdge p) ((onEdge_iff_index t e).mp h).symm⟩

omit [DecidableEq A] [Fintype A] in
theorem indexed_block_triangle_injective (o : BlockIndex A) :
    Function.Injective (indexedBlockTriangle o) := by
  intro t t' h
  have ha : t.1 = t'.1 := congrArg (fun q : OrderedTriangle (IndexedCore A) => q.1.1.2) h
  have hb : t.2.1 = t'.2.1 := congrArg (fun q : OrderedTriangle (IndexedCore A) => q.2.1.1.2) h
  have hc : t.2.2 = t'.2.2 := congrArg (fun q : OrderedTriangle (IndexedCore A) => q.2.2.1.2) h
  exact Prod.ext ha (Prod.ext hb hc)

theorem indexed_triangle_origin (t : OrderedTriangle (IndexedCore A))
    (hc : t.1.1.1 = 0 ∧ t.2.1.1.1 = 1 ∧ t.2.2.1.1 = 2)
    (he : triangleEdges t ⊆ (indexedResidual A).edgeFinset) :
    ∃ o k, k ∈ triangles ∧ indexedBlockTriangle o k = t := by
  have h01 := SimpleGraph.mem_edgeFinset.mp (he (show s(t.1,t.2.1) ∈ triangleEdges t by
    simp [triangleEdges]))
  have h02 := SimpleGraph.mem_edgeFinset.mp (he (show s(t.1,t.2.2) ∈ triangleEdges t by
    simp [triangleEdges]))
  have h12 := SimpleGraph.mem_edgeFinset.mp (he (show s(t.2.1,t.2.2) ∈ triangleEdges t by
    simp [triangleEdges]))
  obtain ⟨a,b,c,ha,hb,hc'⟩ := indexed_triangle_localizes hc.1 hc.2.1 hc.2.2 h01 h02 h12
  let o : BlockIndex A := (a,b,c)
  let k : Triangle := (t.1.1.2,t.2.1.1.2,t.2.2.1.2)
  have heq : indexedBlockTriangle o k = t := by
    apply Prod.ext
    · exact Prod.ext (Prod.ext hc.1.symm rfl) ha.symm
    · exact Prod.ext (Prod.ext (Prod.ext hc.2.1.symm rfl) hb.symm)
        (Prod.ext (Prod.ext hc.2.2.symm rfl) hc'.symm)
  have hpart (i : Fin 3) : onTriangleIndex k i ∈ edges := by
    apply (indexed_block_edge_mem o _).mp
    apply he
    rw [← heq,indexed_block_triangle_edges]
    exact mem_image.mpr ⟨i,mem_univ _,rfl⟩
  exact ⟨o,k,mem_filter.mpr ⟨mem_univ _,(hpart 0),(hpart 1),(hpart 2)⟩,heq⟩

end SplitGapIV
