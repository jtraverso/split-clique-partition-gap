module

public import LocalLemmaLib.Coin
public import R434.AffineH54

@[expose] public section

namespace SplitGapIV

open Finset MeasureTheory ProbabilityTheory GapExtremal.R434.H54
open scoped ENNReal

variable {A : Type*}

/-- The two stored keys are (a,b), (a,c) and (b,c) in the three respective colors. -/
abbrev IndexedCore (A : Type*) := Role × A × A

def sharedKey (x : IndexedCore A) (c : Fin 3) : A :=
  if c = 0 ∨ (x.1.1 = 0 ∧ c = 1) then x.2.1 else x.2.2

def indexedResidual (A : Type*) : SimpleGraph (IndexedCore A) where
  Adj x y := roleGraph.Adj x.1 y.1 ∧ sharedKey x y.1.1 = sharedKey y x.1.1
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

instance [DecidableEq A] : DecidableRel (indexedResidual A).Adj :=
  fun x y => inferInstanceAs (Decidable
    (roleGraph.Adj x.1 y.1 ∧ sharedKey x y.1.1 = sharedKey y x.1.1))

/-- A triangle uses the same three indices in the two roles in which each index appears. -/
theorem indexed_triangle_localizes {x y z : IndexedCore A}
    (hx : x.1.1 = 0) (hy : y.1.1 = 1) (hz : z.1.1 = 2)
    (hxy : (indexedResidual A).Adj x y) (hxz : (indexedResidual A).Adj x z)
    (hyz : (indexedResidual A).Adj y z) :
    ∃ a b c : A, x.2 = (a,b) ∧ y.2 = (a,c) ∧ z.2 = (b,c) := by
  have ha : x.2.1 = y.2.1 := by simpa [sharedKey,hx,hy] using hxy.2
  have hb : x.2.2 = z.2.1 := by simpa [sharedKey,hx,hz] using hxz.2
  have hc : y.2.2 = z.2.2 := by simpa [sharedKey,hy,hz] using hyz.2
  exact ⟨x.2.1,x.2.2,y.2.2, rfl, Prod.ext ha.symm rfl, Prod.ext hb.symm hc.symm⟩

abbrev IndexedTemplate (A : Type*) := (Role × Role) × (A → Bool)

variable [Fintype A] [DecidableEq A]

/-- For adjacent roles a shared key is admitted on just one side. For nonadjacent roles
the template keeps the entire two roles. -/
def indexedPalette (t : IndexedTemplate A) : Finset (IndexedCore A) :=
  univ.filter fun x =>
    if roleGraph.Adj t.1.1 t.1.2 then
      (x.1 = t.1.1 ∧ t.2 (sharedKey x t.1.2.1) = false) ∨
      (x.1 = t.1.2 ∧ t.2 (sharedKey x t.1.1.1) = true)
    else x.1 = t.1.1 ∨ x.1 = t.1.2

omit [DecidableEq A] in
theorem indexed_palette_independent (t : IndexedTemplate A)
    (x y : IndexedCore A) (hx : x ∈ indexedPalette t) (hy : y ∈ indexedPalette t) :
    ¬ (indexedResidual A).Adj x y := by
  intro had
  change roleGraph.Adj x.1 y.1 ∧ sharedKey x y.1.1 = sharedKey y x.1.1 at had
  simp only [indexedPalette,mem_filter,mem_univ,true_and] at hx hy
  split_ifs at hx hy with ht
  · rcases hx with ⟨hx, hxb⟩ | ⟨hx, hxb⟩ <;> rcases hy with ⟨hy, hyb⟩ | ⟨hy,hyb⟩
    · exact had.1.ne (hx.trans hy.symm)
    · have hkey := congrArg t.2 had.2
      rw [hy,hx,hxb,hyb] at hkey
      contradiction
    · have hkey := congrArg t.2 had.2
      rw [hy,hx,hxb,hyb] at hkey
      contradiction
    · exact had.1.ne (hx.trans hy.symm)
  · rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact had.1.ne (hx.trans hy.symm)
    · exact ht (by simpa [hx,hy] using had.1)
    · exact ht (by simpa [hx,hy] using had.1.symm)
    · exact had.1.ne (hx.trans hy.symm)

noncomputable def indexedTemplateMeasure : Measure (IndexedTemplate A) :=
  (PMF.uniformOfFintype (Role × Role)).toMeasure.prod (LocalLemma.coinMeasure A)

instance : IsProbabilityMeasure (indexedTemplateMeasure (A := A)) := by
  unfold indexedTemplateMeasure
  infer_instance

private theorem fair_bit_pair {a b : A} (hab : a ≠ b) :
    LocalLemma.coinMeasure A {f | f a = false ∧ f b = true} = 1/4 := by
  classical
  let ν := LocalLemma.coinMeasure A
  let X (i : A) (f : A → Bool) := f i
  have hind : iIndepFun X ν := iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  have hc (a : A) (v : Bool) : ν (X a ⁻¹' {v}) = 1/2 := by
    change LocalLemma.coinMeasure A ((fun f : A → Bool => f a) ⁻¹' {v}) = _
    rw [← Measure.map_apply (measurable_pi_apply a) (measurableSet_singleton v)]
    change Measure.map (Function.eval a) (LocalLemma.coinMeasure A) {v} = _
    rw [LocalLemma.coinMeasure, Measure.pi_map_eval]
    simp [PMF.uniformOfFintype_apply, one_div,
      ENNReal.mul_inv_cancel (show (2:ℝ≥0∞) ≠ 0 by norm_num) (by simp)]
  have he := (hind.indepFun hab).meas_inter (s := X a ⁻¹' {false}) (t := X b ⁻¹' {true})
    ⟨{false}, measurableSet_singleton _, rfl⟩ ⟨{true}, measurableSet_singleton _, rfl⟩
  change ν {f | f a = false ∧ f b = true} = _ at he
  rw [he, hc, hc]
  apply (ENNReal.toReal_eq_toReal_iff' (ENNReal.mul_ne_top (by simp) (by simp)) (by simp)).mp
  norm_num [one_div, ENNReal.toReal_mul, ENNReal.toReal_inv]

theorem indexed_palette_coverage {x y : IndexedCore A} (hxy : ¬ (indexedResidual A).Adj x y) :
    (1:ℝ)/900 ≤ (indexedTemplateMeasure (A := A)).real {t | ({x,y}:Finset _ ) ⊆ indexedPalette t} := by
  classical
  let D : Set (A → Bool) := if roleGraph.Adj x.1 y.1 then
      {f | f (sharedKey x y.1.1) = false ∧ f (sharedKey y x.1.1) = true} else Set.univ
  let R : Set (IndexedTemplate A) := {(x.1,y.1)} ×ˢ D
  have hD : (1/4 : ℝ≥0∞) ≤ LocalLemma.coinMeasure A D := by
    by_cases he : roleGraph.Adj x.1 y.1
    · have hkeys : sharedKey x y.1.1 ≠ sharedKey y x.1.1 := fun h => hxy ⟨he,h⟩
      rw [show D = _ from ite_eq_left he, fair_bit_pair hkeys]
    · simp [D,he]
  have hsub : R ⊆ {t | ({x,y}:Finset _) ⊆ indexedPalette t} := by
    rintro ⟨⟨r,s⟩,f⟩ ht
    have hr : r = x.1 := congrArg Prod.fst (Set.mem_singleton_iff.mp ht.1)
    have hs : s = y.1 := congrArg Prod.snd (Set.mem_singleton_iff.mp ht.1)
    subst r
    subst s
    by_cases he : roleGraph.Adj x.1 y.1
    · have hh : f (sharedKey x y.1.1) = false ∧ f (sharedKey y x.1.1) = true := by
        simpa [D,he] using ht.2
      simp [indexedPalette,he,hh.1,hh.2,insert_subset_iff]
    · simp [indexedPalette,he,insert_subset_iff]
  let μ := indexedTemplateMeasure (A := A)
  change _ ≤ μ.real _
  apply le_trans _ (measureReal_mono hsub (measure_ne_top μ _))
  have hmass : ((PMF.uniformOfFintype (Role × Role)).toMeasure) {(x.1,y.1)} = 1/225 := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp [PMF.uniformOfFintype_apply,Role]
  have hprod : μ R = (1/225 : ℝ≥0∞)*LocalLemma.coinMeasure A D := by
    change (((PMF.uniformOfFintype (Role × Role)).toMeasure).prod (LocalLemma.coinMeasure A))
      ({(x.1,y.1)} ×ˢ D) = _
    rw [Measure.prod_prod, hmass]
  rw [measureReal_def, hprod]
  have hfinite : LocalLemma.coinMeasure A D ≠ ⊤ := measure_ne_top _ _
  have hreal := ENNReal.toReal_mono hfinite hD
  rw [ENNReal.toReal_mul]
  norm_num at hreal ⊢
  linarith

end SplitGapIV
