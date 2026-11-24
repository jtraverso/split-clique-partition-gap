module

public import QuadraticExteriorPalomar.ExactTransfer
public import GalvinMultigraph.Main
public import PaperVIVendor.HaggkvistJanssen

@[expose] public section

namespace SplitGapIII
open Finset GapExtremal QuadraticExteriorPalomar

variable {V H G : Type*}

/-- A request is a core pair. Equal host choices at an endpoint must be the same request. -/
def Assigned (N : H → Finset V) (J : Finset (Finset V)) (host : J → H) : Prop :=
  (∀ e, e.val ⊆ N (host e)) ∧
  ∀ e f, host e = host f → ∀ v ∈ e.val, v ∈ f.val → e = f

/-- Existing endpoint and list budgets imply a coloring of every bipartite group. -/
theorem recover_bipartite {A R E : Type*} [Finite A] [Finite R] [Finite E]
    (left : E → A) (right : E → R) (N : E → Finset H) (k : ℕ)
    (hleft : ∀ a, Nat.card {e // left e = a} ≤ k)
    (hright : ∀ r, Nat.card {e // right e = r} ≤ k)
    (hN : ∀ e, k ≤ (N e).card) :
    ∃ host : E → H, (∀ e, host e ∈ N e) ∧ GalvinMultigraph.Proper left right host :=
  GalvinMultigraph.galvin_of_degree_bound left right k hleft hright N hN

/-- An injective midpoint label at each endpoint bounds both fiber degrees by its palette. -/
theorem recover_bipartite_from_midpoints {A R E S : Type*}
    [Finite A] [Finite R] [Finite E] [Fintype S]
    (left : E → A) (right : E → R) (midpoint : E → S)
    (hm : GalvinMultigraph.Proper left right midpoint)
    (lists : E → Finset H) (hlists : ∀ e, Fintype.card S ≤ (lists e).card) :
    ∃ host : E → H, (∀ e, host e ∈ lists e) ∧ GalvinMultigraph.Proper left right host := by
  have h := GalvinMultigraph.degree_bounds_of_proper left right midpoint hm
  exact recover_bipartite left right lists _ h.1 h.2 hlists

/-- A complete group, including the final clique of padding vertices. -/
theorem recover_complete {A : Type*} [Fintype A] [DecidableEq A]
    (lists : (⊤ : SimpleGraph A).edgeSet → Finset H)
    (h : ∀ e, Fintype.card A ≤ (lists e).card) :
    ∃ color : (⊤ : SimpleGraph A).lineGraph.Coloring H, ∀ e, color e ∈ lists e :=
  HaggkvistJanssen.exists_listEdgeColoring_complete lists h

/-- Deleting two sets of colors from a list costs at most the sum of their sizes. -/
theorem trim_two_lists [DecidableEq H] (available occupiedA occupiedB : Finset H) (due : ℕ)
    (budget : due + occupiedA.card + occupiedB.card ≤ available.card) :
    due ≤ (available \ (occupiedA ∪ occupiedB)).card := by
  have hunion := Finset.card_union_le occupiedA occupiedB
  have hsplit := Finset.card_sdiff_add_card_eq_card
    (show available ∩ (occupiedA ∪ occupiedB) ⊆ available from Finset.inter_subset_left)
  have hcard := Finset.card_le_card
    (show available ∩ (occupiedA ∪ occupiedB) ⊆ occupiedA ∪ occupiedB from Finset.inter_subset_right)
  have hsame : available \ (available ∩ (occupiedA ∪ occupiedB)) =
      available \ (occupiedA ∪ occupiedB) := by
    ext x
    simp only [mem_sdiff, mem_inter]
    tauto
  rw [hsame] at hsplit
  omega

/-- Disjoint sets of hosts let us compose local solutions even when groups share core vertices. -/
theorem assemble_groups (N : H → Finset V) (J : Finset (Finset V))
    (group : J → G) (palette : G → Finset H)
    (hdisj : ∀ g g', g ≠ g' → Disjoint (palette g) (palette g'))
    (solve : ∀ g, ∃ c : {e : J // group e = g} → H,
      (∀ e, c e ∈ palette g ∧ e.val.val ⊆ N (c e)) ∧
      ∀ e f, c e = c f → ∀ v ∈ e.val.val, v ∈ f.val.val → e = f) :
    ∃ host : J → H, Assigned N J host := by
  choose choice hchoice hproper using solve
  let host (e : J) := choice (group e) ⟨e, rfl⟩
  refine ⟨host, fun e => (hchoice (group e) ⟨e, rfl⟩).2, ?_⟩
  intro e f hhost v hev hfv
  have same : group e = group f := by
    by_contra h
    have he : host e ∈ palette (group e) := (hchoice (group e) ⟨e, rfl⟩).1
    have hf : host f ∈ palette (group f) := (hchoice (group f) ⟨f, rfl⟩).1
    rw [← hhost] at hf
    exact (Finset.disjoint_left.mp (hdisj _ _ h)) he hf
  have compare (g g' : G) (hg : g = g') (p : {e : J // group e = g})
      (q : {e : J // group e = g'}) (hc : choice g p = choice g' q)
      (hv : v ∈ p.val.val) (hw : v ∈ q.val.val) : p.val = q.val := by
    subst g'
    exact congrArg Subtype.val (hproper g p q hc v hv hw)
  exact compare _ _ same ⟨e, rfl⟩ ⟨f, rfl⟩ hhost hev hfv

/-- An independently solved terminal set can reuse hosts if it avoids the used endpoint ports. -/
theorem assemble_prefix_and_terminal_preserving [DecidableEq V] (N : H → Finset V) (J P T : Finset (Finset V))
    (cover : ∀ e ∈ J, e ∈ P ∨ e ∈ T)
    (first : P → H) (terminal : T → H)
    (hp : Assigned N P first) (ht : Assigned N T terminal)
    (avoid : ∀ e f, first e = terminal f → ∀ v ∈ (e : P).val, v ∉ (f : T).val) :
    ∃ host : J → H, Assigned N J host ∧
      ∀ (e : J) (he : e.val ∈ P), host e = first ⟨e.val, he⟩ := by
  classical
  let host (e : J) : H :=
    if he : e.val ∈ P then first ⟨e.val, he⟩
    else terminal ⟨e.val, (cover e.val e.property).resolve_left he⟩
  refine ⟨host, ⟨?_, ?_⟩, ?_⟩
  · intro e
    unfold host
    split
    · rename_i he
      exact hp.1 ⟨e.val, he⟩
    · rename_i he
      exact ht.1 ⟨e.val, (cover e.val e.property).resolve_left he⟩
  · intro e f hh v he hf
    apply Subtype.ext
    unfold host at hh
    split at hh <;> split at hh
    · exact congrArg (fun p : P => p.val) (hp.2 _ _ hh v he hf)
    · exact (avoid _ _ hh v he hf).elim
    · exact (avoid _ _ hh.symm v hf he).elim
    · exact congrArg (fun p : T => p.val) (ht.2 _ _ hh v he hf)
  · intro e he
    simp [host, he]

/-- An independently solved terminal set can reuse hosts if it avoids the used endpoint ports. -/
theorem assemble_prefix_and_terminal [DecidableEq V] (N : H → Finset V) (J P T : Finset (Finset V))
    (cover : ∀ e ∈ J, e ∈ P ∨ e ∈ T)
    (first : P → H) (terminal : T → H)
    (hp : Assigned N P first) (ht : Assigned N T terminal)
    (avoid : ∀ e f, first e = terminal f → ∀ v ∈ (e : P).val, v ∉ (f : T).val) :
    ∃ host : J → H, Assigned N J host := by
  obtain ⟨host, hall, _⟩ :=
    assemble_prefix_and_terminal_preserving N J P T cover first terminal hp ht avoid
  exact ⟨host, hall⟩

/-- Every complete physical reassignment preserves the exact residual gap. -/
theorem gap_of_complete_recovery [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H] (B : SimpleGraph V) [DecidableRel B.Adj]
    (N : H → Finset V) (independent : ∀ h, ∀ a ∈ N h, ∀ b ∈ N h, ¬ B.Adj a b)
    (host : jPairs B univ → H) (hhost : Assigned N (jPairs B univ) host) :
    gap (hostGraph N) = residualSup B - residualInt B := by
  have h := gap_stability_of_partial_assignment B N independent _ (Subset.rfl) host hhost.1 hhost.2
  simp only [Nat.sub_self, Nat.cast_zero, mul_zero, abs_nonpos_iff, sub_eq_zero] at h
  exact h

/-- A common sum determines the other endpoint. Cancellation suffices on the position type. -/
theorem midpoint_label_proper {E A : Type*} [AddGroup A]
    (left right : E → A) (sumLabel : E → A)
    (hsum : ∀ e, sumLabel e = left e + right e)
    (hpair : ∀ e f, left e = left f → right e = right f → e = f) :
    GalvinMultigraph.Proper left right sumLabel := by
  intro e f hne hside heq
  have hab : left e + right e = left f + right f := by
    rw [← hsum e, ← hsum f, heq]
  apply hne
  rcases hside with hl | hr
  · exact hpair e f hl (add_left_cancel (hl ▸ hab))
  · exact hpair e f (add_right_cancel (hr ▸ hab)) hr

/-- A recovered color gives a triangle using only surviving physical incidences. -/
theorem recover_physical_bipartite_group [Finite V] [DecidableEq V]
    {S : Type*} [Fintype S] (N : H → Finset V) (J : Finset (Finset V))
    (left right : J → V) (midpoint : J → S)
    (ends : ∀ e, e.val = {left e, right e})
    (sides : ∀ e f, left e ≠ right f)
    (hmid : GalvinMultigraph.Proper left right midpoint)
    (lists : J → Finset H)
    (listsPhysical : ∀ e h, h ∈ lists e → e.val ⊆ N h)
    (listsLarge : ∀ e, Fintype.card S ≤ (lists e).card) :
    ∃ host : J → H, Assigned N J host := by
  obtain ⟨host, hlist, hproper⟩ :=
    recover_bipartite_from_midpoints left right midpoint hmid lists listsLarge
  refine ⟨host, fun e => listsPhysical e _ (hlist e), ?_⟩
  intro e f hh v he hf
  by_contra hne
  apply hproper e f hne _ hh
  rw [ends e, Finset.mem_insert, Finset.mem_singleton] at he
  rw [ends f, Finset.mem_insert, Finset.mem_singleton] at hf
  rcases he with he | he <;> rcases hf with hf | hf
  · exact Or.inl (he.symm.trans hf)
  · exact (sides e f (he.symm.trans hf)).elim
  · exact (sides f e (hf.symm.trans he)).elim
  · exact Or.inr (he.symm.trans hf)

end SplitGapIII
