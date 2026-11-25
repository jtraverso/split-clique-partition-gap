module

public import LocalLemmaLib.LocalLemma
public import SplitGapIII.Reassignment

@[expose] public section

namespace SplitGapIV

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- With at most 4Lb intersecting events per conflict, L ≥ 12b gives the LLL budget. -/
theorem local_conflict_budget (L b d : ℕ) (hL : 12 * b ≤ L)
    (hd : d + 1 ≤ 4 * L * b) : Real.exp 1 * ((d : ℝ) + 1) ≤ (L : ℝ)^2 := by
  have hL' : 12 * (b : ℝ) ≤ L := by exact_mod_cast hL
  have hd' : (d : ℝ) + 1 ≤ 4 * (L : ℝ) * b := by exact_mod_cast hd
  calc
    _ ≤ 3 * ((d : ℝ) + 1) := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (by positivity)
    _ ≤ _ := by nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) L) (sub_nonneg.mpr hL')]

/-- Independent choices from lists of length L avoid binary conflicts if their
dependency degree is at most d and e(d+1) ≤ L². -/
theorem exists_avoids_host_conflicts {E : Type*} [Fintype E] [DecidableEq E]
    {L m d : ℕ} (hL : 0 < L)
    (left right : Fin m → E) (distinct : ∀ i, left i ≠ right i)
    (a b : Fin m → Fin L) (Γ : SimpleGraph (Fin m)) [DecidableRel Γ.Adj]
    (dep : ∀ i j, j ≠ i → ¬ Γ.Adj i j →
      Disjoint ({left i, right i} : Finset E) {left j, right j})
    (hdegree : ∀ i, Γ.degree i ≤ d)
    (hbudget : Real.exp 1 * (d + 1 : ℝ) ≤ (L : ℝ)^2) :
    ∃ f : E → Fin L, ∀ i, ¬ (f (left i) = a i ∧ f (right i) = b i) := by
  classical
  let _ : Nonempty (Fin L) := ⟨⟨0,hL⟩⟩
  let ν := (PMF.uniformOfFintype (Fin L)).toMeasure
  let νs : E → Measure (Fin L) := fun _ => ν
  let μ := Measure.pi νs
  have : ∀ e, IsProbabilityMeasure (νs e) := inferInstance
  have : IsProbabilityMeasure μ := inferInstance
  let A (i : Fin m) : Set (E → Fin L) := {f | f (left i) = a i ∧ f (right i) = b i}
  let S (i : Fin m) : Finset E := {left i, right i}
  let eval (e : E) (f : E → Fin L) := f e
  have hind : iIndepFun eval μ := by
    exact iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  let coord (T : Finset E) := MeasurableSpace.comap
    (fun (f : E → Fin L) (e : T) => f e) MeasurableSpace.pi
  have hcoord (T : Finset E) (i : Fin m) (hT : S i ⊆ T) :
      MeasurableSet[coord T] (A i) := by
    let l : T := ⟨left i, hT (by simp [S])⟩
    let r : T := ⟨right i, hT (by simp [S])⟩
    refine ⟨{g : T → Fin L | g l = a i ∧ g r = b i}, (Set.toFinite _).measurableSet, ?_⟩
    rfl
  have hdep : LocalLemma.IsDependencyGraph μ A Γ := by
    intro i
    have hind' := hind.indepFun_finset (S i) (S i)ᶜ disjoint_compl_right
      (fun e => measurable_pi_apply e)
    have hc : Indep (coord (S i)) (coord (S i)ᶜ) μ :=
      (IndepFun_iff_Indep _ _ _).1 hind'
    have hleft : MeasurableSpace.generateFrom {A i} ≤ coord (S i) := by
      refine MeasurableSpace.generateFrom_le fun t ht => ?_
      obtain rfl := Set.mem_singleton_iff.mp ht
      exact hcoord (S i) i (Subset.refl _)
    have hright : MeasurableSpace.generateFrom
        {t | ∃ j, j ≠ i ∧ ¬ Γ.Adj i j ∧ t = A j} ≤ coord (S i)ᶜ := by
      refine MeasurableSpace.generateFrom_le ?_
      rintro t ⟨j, hji, had, rfl⟩
      apply hcoord _ j
      intro e he
      exact mem_compl.mpr fun he' => disjoint_left.mp (dep i j hji had) he' he
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hc hleft) hright
  have hsingle (e : E) (c : Fin L) : μ (eval e ⁻¹' {c}) = (L : ℝ≥0∞)⁻¹ := by
    change (Measure.pi νs) ((fun f : E → Fin L => f e) ⁻¹' {c}) = _
    rw [← Measure.map_apply (measurable_pi_apply e) (measurableSet_singleton c)]
    change Measure.map (Function.eval e) (Measure.pi νs) {c} = _
    rw [Measure.pi_map_eval]
    have hmass (j : E) : νs j Set.univ = 1 := measure_univ
    simp only [hmass, prod_const_one, one_smul]
    rw [show νs e = (PMF.uniformOfFintype (Fin L)).toMeasure by rfl,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp [PMF.uniformOfFintype_apply]
  have hprob (i : Fin m) : μ.real (A i) ≤ ((L : ℝ)^2)⁻¹ := by
    have hAB := (hind.indepFun (distinct i)).meas_inter
      (s := eval (left i) ⁻¹' {a i}) (t := eval (right i) ⁻¹' {b i})
      ⟨{a i}, measurableSet_singleton _, rfl⟩ ⟨{b i}, measurableSet_singleton _, rfl⟩
    change μ (A i) = μ (eval (left i) ⁻¹' {a i}) * μ (eval (right i) ⁻¹' {b i}) at hAB
    rw [measureReal_def, hAB, hsingle, hsingle, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast, ← pow_two, inv_pow]
  have hpos := LocalLemma.lll_symmetric μ A (fun _ => (Set.toFinite _).measurableSet) Γ hdep
    hprob hdegree (by
      have hpos : 0 < (L : ℝ)^2 := by positivity
      calc
        _ = (Real.exp 1 * ((d : ℝ) + 1)) / (L : ℝ)^2 := by ring
        _ ≤ 1 := (div_le_one hpos).2 hbudget)
  have hne : (⋂ i, (A i)ᶜ).Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn, measureReal_empty] at hpos
    exact (lt_irrefl 0) hpos
  obtain ⟨f,hf⟩ := hne
  exact ⟨f, fun i => Set.mem_iInter.mp hf i⟩

/-- A certificate listing all physical two-request conflicts yields a proper assignment. -/
theorem assigned_of_conflict_certificate {V H : Type*} [DecidableEq V]
    (J : Finset (Finset V)) (N : H → Finset V)
    {L m d : ℕ} (hL : 0 < L)
    (lists : J → Fin L → H) (available : ∀ e c, e.val ⊆ N (lists e c))
    (left right : Fin m → J) (distinct : ∀ i, left i ≠ right i)
    (a b : Fin m → Fin L)
    (complete : ∀ e f c c', e ≠ f → (∃ v, v ∈ e.val ∧ v ∈ f.val) →
      lists e c = lists f c' →
        ∃ i, left i = e ∧ right i = f ∧ a i = c ∧ b i = c')
    (Γ : SimpleGraph (Fin m)) [DecidableRel Γ.Adj]
    (dep : ∀ i j, j ≠ i → ¬ Γ.Adj i j →
      Disjoint ({left i, right i} : Finset J) {left j, right j})
    (hdegree : ∀ i, Γ.degree i ≤ d)
    (hbudget : Real.exp 1 * (d + 1 : ℝ) ≤ (L : ℝ)^2) :
    ∃ host : J → H, SplitGapIII.Assigned N J host := by
  classical
  obtain ⟨f, hf⟩ := exists_avoids_host_conflicts hL left right distinct a b Γ dep hdegree hbudget
  refine ⟨fun e => lists e (f e), fun e => available e (f e), ?_⟩
  intro e e' hhost v hv hv'
  by_contra hne
  obtain ⟨i, hi, hi', ha, hb⟩ := complete e e' (f e) (f e') hne ⟨v,hv,hv'⟩ hhost
  exact hf i ⟨by rw [hi, ha], by rw [hi', hb]⟩

end SplitGapIV
