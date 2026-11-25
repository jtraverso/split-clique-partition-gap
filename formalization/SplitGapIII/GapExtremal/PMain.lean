/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license.
Authors: Juan Pablo Traverso Gianini
-/
module

public import GapExtremal.PHosts
public import GapExtremal.Main

/-!
# The gap of a positioned construction (ledger Cor. 16.4)

`gap (hostGraph (ppalette D C S)) ≥ |C| · |W| / 3` for every cap `C` with a separating family `S`, on any
positioned core satisfying the twin condition `hsame`.
-/

@[expose] public section

namespace GapExtremal

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [AddCommGroup W] [Module F W] [Fintype W] [DecidableEq W]
variable {V P : Type*} [Fintype V] [DecidableEq V] [Fintype P] [DecidableEq P]
variable {U : Type*} [AddCommGroup U] [Module F U] [Fintype U] [DecidableEq U]

/-- **Cor. 16.4.** -/
theorem pgap_ge_third (D : PData F W V P) {C : Finset W} (hC : IsCap F (C : Set W)) (hC0 : C.Nonempty)
    (S : SepFam F C U)
    (hsame : ∀ v v', D.base v = D.base v' → ∀ i j, D.σ i = D.pos v → D.σ j = D.pos v' →
      ¬ H12.graph.Adj i j) :
    ((C.card * Fintype.card W : ℕ) : ℝ) / 3 ≤ gap (hostGraph (ppalette D C S)) := by
  have h := gap_ge (phostHyp (S := S) hC0 hsame) (8 * (pblocks D C).card)
    (fun T hT => pI_le D hC hT) (presPack (D := D) (C := C))
  have hv := pvalue (D := D) (C := C)
  have hb : ((pblocks D C).card : ℝ) ≤ C.card * Fintype.card W := by
    exact_mod_cast card_pblocks_le D
  push_cast at h ⊢
  linarith

/-- Order of a positioned construction. -/
theorem pcard_vertices :
    Fintype.card (V ⊕ PHostIdx F W P U) =
      Fintype.card V + Fintype.card (F × W) * (Fintype.card U * Fintype.card F * Fintype.card (Sym2 P))
        + Fintype.card (F × W) * Fintype.card (Sym2 P) := by
  simp only [PHostIdx, Fintype.card_sum, Fintype.card_prod]
  ring

end GapExtremal
