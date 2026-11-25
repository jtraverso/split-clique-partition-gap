module

public import SplitGapIV.ListCompletion
public import SplitGapIV.RecoveryBound

@[expose] public section

namespace SplitGapIV

open Finset

variable {V H : Type*} [DecidableEq V] [Fintype H] [DecidableEq H]

/-- Hosts physically complete to a pair. -/
def availableHosts (N : H → Finset V) (e : Finset V) : Finset H :=
  univ.filter fun h => e ⊆ N h

/-- A uniform local degree bound follows from the size of a live host neighborhood. -/
theorem assigned_of_surviving_lists
    (J : Finset (Finset V)) (N : H → Finset V) (htwo : ∀ e ∈ J, e.card = 2)
    {L b : ℕ} (hL : 0 < L) (hbudget : 24*b ≤ L)
    (listsLower : ∀ e ∈ J, L ≤ (availableHosts N e).card)
    (neighborhoodUpper : ∀ h, (N h).card ≤ b) :
    ∃ host : J → H, SplitGapIII.Assigned N J host := by
  classical
  let slot (e : J) (c : Fin L) : availableHosts N e.val :=
    (Fintype.equivFin (availableHosts N e.val)).symm
      (Fin.castLE (by simpa only [Fintype.card_coe] using listsLower e.val e.property) c)
  let lists (e : J) (c : Fin L) : H := (slot e c).val
  have available (e : J) (c : Fin L) : e.val ⊆ N (lists e c) :=
    (mem_filter.mp (slot e c).property).2
  have hinj (e : J) : Function.Injective (lists e) := by
    intro c d he
    have hslot : slot e c = slot e d := Subtype.ext he
    have hcast := (Fintype.equivFin (availableHosts N e.val)).symm.injective hslot
    exact Fin.ext (congrArg (fun z : Fin (Fintype.card (availableHosts N e.val)) => z.val) hcast)
  apply assigned_of_local_list_capacity J N htwo hL hbudget lists available
  intro v h
  let T := (univ : Finset (J × Fin L)).filter
    (fun x => v ∈ x.1.val ∧ lists x.1 x.2 = h)
  have hprop (x : T) : v ∈ x.val.1.val ∧ lists x.val.1 x.val.2 = h := (mem_filter.mp x.property).2
  have hother (x : T) : ∃ w ∈ N h, x.val.1.val = {v,w} := by
    obtain ⟨a,c,hac,hac'⟩ := card_eq_two.mp (htwo x.val.1.val x.val.1.property)
    have hmem : v = a ∨ v = c := by simpa [hac'] using (hprop x).1
    have hs := available x.val.1 x.val.2
    rw [(hprop x).2] at hs
    rcases hmem with rfl | rfl
    · exact ⟨c, hs (by simp [hac']), hac'⟩
    · exact ⟨a, hs (by simp [hac']), by rw [hac', pair_comm]⟩
  let f (x : T) : N h := ⟨(hother x).choose, (hother x).choose_spec.1⟩
  have hf : Function.Injective f := by
    intro x y he
    have hw := congrArg (fun p : N h => p.val) he
    have hs : x.val.1 = y.val.1 := Subtype.ext (by
      rw [(hother x).choose_spec.2, (hother y).choose_spec.2]
      change (hother x).choose = (hother y).choose at hw
      rw [hw])
    have hc : x.val.2 = y.val.2 := hinj x.val.1 (by
      rw [(hprop x).2, hs, (hprop y).2])
    exact Subtype.ext (Prod.ext hs hc)
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe, Fintype.card_coe] at hcard
  exact hcard.trans (neighborhoodUpper h)

end SplitGapIV
