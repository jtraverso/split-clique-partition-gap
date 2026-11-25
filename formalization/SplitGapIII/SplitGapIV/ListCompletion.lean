module

public import SplitGapIV.LocalCompletion

@[expose] public section

namespace SplitGapIV

open Finset

variable {V H : Type*} [DecidableEq V] [DecidableEq H]

/-- Build the complete dependency graph from the physical lists. The cap counts slots
at a vertex and a host, including the slot that is being tested. -/
theorem assigned_of_local_list_capacity
    (J : Finset (Finset V)) (N : H → Finset V)
    (htwo : ∀ e ∈ J, e.card = 2) {L b : ℕ} (hL : 0 < L) (hbudget : 24 * b ≤ L)
    (lists : J → Fin L → H) (available : ∀ e c, e.val ⊆ N (lists e c))
    (cap : ∀ v h, ((univ : Finset (J × Fin L)).filter
      (fun x => v ∈ x.1.val ∧ lists x.1 x.2 = h)).card ≤ b) :
    ∃ host : J → H, SplitGapIII.Assigned N J host := by
  classical
  let Z := J × Fin L
  let color (x : Z) := lists x.1 x.2
  let touch (x : Z) : Finset Z := univ.filter fun y =>
    ¬ Disjoint x.1.val y.1.val ∧ color x = color y
  have htouch (x : Z) : (touch x).card ≤ 2*b := by
    let hits (v : V) : Finset Z := univ.filter fun y => v ∈ y.1.val ∧ color y = color x
    have hsub : touch x ⊆ x.1.val.biUnion hits := by
      intro y hy
      have hy' := (mem_filter.mp hy).2
      obtain ⟨v, hv, hv'⟩ : ∃ v ∈ x.1.val, v ∈ y.1.val := by
        simpa [disjoint_left] using hy'.1
      exact mem_biUnion.mpr ⟨v, hv, mem_filter.mpr ⟨mem_univ _, hv', hy'.2.symm⟩⟩
    calc
      _ ≤ (x.1.val.biUnion hits).card := card_le_card hsub
      _ ≤ ∑ v ∈ x.1.val, (hits v).card := card_biUnion_le
      _ ≤ ∑ _v ∈ x.1.val, b := sum_le_sum fun v _ => cap v (color x)
      _ = _ := by simp [htwo x.1.val x.1.property]
  let outgoing (e : J) : Finset (Z × Z) :=
    univ.biUnion fun c : Fin L => (touch (e,c)).image fun y => ((e,c),y)
  have hout (e : J) : (outgoing e).card ≤ 2*L*b := by
    calc
      _ ≤ ∑ c : Fin L, ((touch (e,c)).image (fun y => ((e,c),y))).card := card_biUnion_le
      _ ≤ ∑ _c : Fin L, 2*b := sum_le_sum fun c _ => card_image_le.trans (htouch (e,c))
      _ = _ := by simp; ring
  let C : Finset (Z × Z) := univ.filter fun xy =>
    xy.1.1 ≠ xy.2.1 ∧ xy.2 ∈ touch xy.1
  let m := Fintype.card C
  let enum : Fin m ≃ C := (Fintype.equivFin C).symm
  let pair (i : Fin m) : Z × Z := (enum i).val
  let left (i : Fin m) : J := (pair i).1.1
  let right (i : Fin m) : J := (pair i).2.1
  let S (i : Fin m) : Finset J := {left i, right i}
  have hpair (i : Fin m) : left i ≠ right i ∧ (pair i).2 ∈ touch (pair i).1 :=
    (mem_filter.mp (enum i).property).2
  by_cases hm : m = 0
  · let slot : Fin L := ⟨0,hL⟩
    refine ⟨fun e => lists e slot, fun e => available e slot, ?_⟩
    intro e f h v he hf
    by_contra hne
    have hc : ((e,slot),(f,slot)) ∈ C := mem_filter.mpr
      ⟨mem_univ _, hne, mem_filter.mpr ⟨mem_univ _, fun hd =>
        disjoint_left.mp hd he hf, h⟩⟩
    have hi := (enum.symm ⟨_,hc⟩).isLt
    omega
  let Γ : SimpleGraph (Fin m) :=
    { Adj := fun i j => i ≠ j ∧ ¬ Disjoint (S i) (S j)
      symm := ⟨fun _ _ h => ⟨h.1.symm, fun hd => h.2 hd.symm⟩⟩
      loopless := ⟨fun _ h => h.1 rfl⟩ }
  have hdegree (i : Fin m) : Γ.degree i + 1 ≤ 8*L*b := by
    let W (e : J) : Finset (Z × Z) := outgoing e ∪ (outgoing e).image Prod.swap
    have hW (e : J) : (W e).card ≤ 4*L*b := by
      have hb := hout e
      calc
        _ ≤ (outgoing e).card + ((outgoing e).image Prod.swap).card := card_union_le _ _
        _ ≤ (outgoing e).card + (outgoing e).card := Nat.add_le_add_left card_image_le _
        _ ≤ _ := by
          calc
            _ ≤ 2 * L * b + 2 * L * b := Nat.add_le_add hb hb
            _ = _ := by ring
    have hWmem (j : Fin m) (e : J) (he : e ∈ S j) : pair j ∈ W e := by
      rcases (mem_insert.mp he) with h | h
      · have h' : e = (pair j).1.1 := h
        rw [h']
        exact mem_union_left _ (mem_biUnion.mpr ⟨(pair j).1.2, mem_univ _,
          mem_image.mpr ⟨(pair j).2, (hpair j).2, by simp⟩⟩)
      · have h' : e = (pair j).2.1 := mem_singleton.mp h
        rw [h']
        apply mem_union_right
        apply mem_image.mpr
        refine ⟨(pair j).swap, ?_, by simp⟩
        apply mem_biUnion.mpr
        refine ⟨(pair j).2.2, mem_univ _, mem_image.mpr ⟨(pair j).1, ?_, rfl⟩⟩
        have ht := (mem_filter.mp (hpair j).2).2
        exact mem_filter.mpr ⟨mem_univ _, (fun hd => ht.1 hd.symm), ht.2.symm⟩
    have hsub : (insert i (Γ.neighborFinset i)).image pair ⊆ W (left i) ∪ W (right i) := by
      intro xy hxy
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hxy
      rcases mem_insert.mp hj with heq | hj
      · subst j
        exact mem_union_left _ (hWmem i (left i) (by simp [S]))
      · have hadj : ¬ Disjoint (S i) (S j) := ((Γ.mem_neighborFinset i j).mp hj).2
        obtain ⟨e,he,he'⟩ : ∃ e ∈ S i, e ∈ S j := by
          simpa [disjoint_left] using hadj
        have hm := hWmem j e he'
        simp only [S, mem_insert, mem_singleton] at he
        rcases he with rfl | rfl
        · exact mem_union_left _ hm
        · exact mem_union_right _ hm
    have hpinj : Function.Injective pair := fun _ _ eq => enum.injective (Subtype.ext eq)
    have hno : i ∉ Γ.neighborFinset i := fun h => ((Γ.mem_neighborFinset i i).mp h).1 rfl
    calc
      _ = (insert i (Γ.neighborFinset i)).card := by
        rw [card_insert_of_notMem hno, SimpleGraph.card_neighborFinset_eq_degree]
      _ = ((insert i (Γ.neighborFinset i)).image pair).card := (card_image_of_injective _ hpinj).symm
      _ ≤ (W (left i) ∪ W (right i)).card := card_le_card hsub
      _ ≤ (W (left i)).card + (W (right i)).card := card_union_le _ _
      _ ≤ _ := by
        calc
          _ ≤ 4 * L * b + 4 * L * b := Nat.add_le_add (hW (left i)) (hW (right i))
          _ = _ := by ring
  have hn : 0 < 8*L*b := by
    have i : Fin m := ⟨0, Nat.pos_of_ne_zero hm⟩
    have h := hdegree i
    omega
  apply assigned_of_conflict_certificate J N hL lists available left right (fun i => (hpair i).1)
    (fun i => (pair i).1.2) (fun i => (pair i).2.2) _ Γ _ _
    (local_conflict_budget L (2*b) (8*L*b-1) (by omega) (by
      rw [show 4 * L * (2*b) = 8*L*b by ring]
      omega))
  · intro e f c c' hne hmeet heq
    have he : ((e,c),(f,c')) ∈ C := mem_filter.mpr ⟨mem_univ _, hne, mem_filter.mpr
      ⟨mem_univ _, fun hd => by
        obtain ⟨v,hv,hv'⟩ := hmeet
        exact disjoint_left.mp hd hv hv', heq⟩⟩
    refine ⟨enum.symm ⟨_, he⟩, ?_⟩
    simp [left,right,pair]
  · intro i j hij hn'
    by_contra h
    exact hn' ⟨Ne.symm hij, h⟩
  · intro i
    have h := hdegree i
    omega

end SplitGapIV
