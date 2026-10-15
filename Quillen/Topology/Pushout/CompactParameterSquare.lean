/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.Pushout.CompactParameter
public import Quillen.Topology.Maps.SumSubtype
public import Quillen.Topology.Realization.DoubleCylinderCompactGraph

/-!
# Actual pushout squares over a locally compact test parameter

The literal matched square has the original pushout universal property when
its matching locus is closed. Its quotient topology comes from the proved
sum-of-legs pullback quotient. Option-valued descent permits empty targets
and noninjective attaching maps.
-/
@[expose] public section

open Topology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits MonoidalCategory
open scoped Topology Simplicial
universe u
namespace Quillen.CompactParameterPushout
variable {A B C P T : TopCat.{u}} {i : A ⟶ B} {f : A ⟶ C} {g : B ⟶ P} {j : C ⟶ P}
  (sq : IsPushout i f g j) (base : C(P, T))
  {D : Type u} [TopologicalSpace D] (b : C(D, T))

/-- The attaching space paired with a test parameter, restricted to pairs whose images under the
base maps agree. -/
abbrev Source : TopCat.{u} := TopCat.of {z : A × D // base (g (i z.1)) = b z.2}
/-- The left corner paired with a test parameter and restricted by the equality `base (g x) = b
d`. -/
abbrev Left : TopCat.{u} := TopCat.of {z : B × D // base (g z.1) = b z.2}
/-- The right corner paired with a test parameter and restricted by the equality `base (j x) = b
d`. -/
abbrev Right : TopCat.{u} := TopCat.of {z : C × D // base (j z.1) = b z.2}
/-- The strict pullback of the pushout base map `base` along the test map `b`. -/
abbrev Vertex : TopCat.{u} := TopCat.of {z : P × D // base z.1 = b z.2}

/-- Retain the test parameter and apply only the original upper leg. -/
def leftLeg : Source (i := i) (g := g) base b ⟶ Left (g := g) base b :=
  TopCat.ofHom ⟨fun z ↦ ⟨(i z.val.1, z.val.2), z.property⟩, by fun_prop⟩

/-- Retain the test parameter and apply only the original lower leg. -/
def rightLeg : Source (i := i) (g := g) base b ⟶ Right (j := j) base b :=
  TopCat.ofHom ⟨fun z ↦ ⟨(f z.val.1, z.val.2),
    (congrArg base (ConcreteCategory.congr_hom sq.w z.val.1)).symm.trans z.property⟩, by fun_prop⟩

/-- Map the matched left corner to the matched vertex by `g`, retaining the test parameter. -/
def leftInclusion : Left (g := g) base b ⟶ Vertex base b :=
  TopCat.ofHom ⟨fun z ↦ ⟨(g z.val.1, z.val.2), z.property⟩, by fun_prop⟩
/-- Map the matched right corner to the matched vertex by `j`, retaining the test parameter. -/
def rightInclusion : Right (j := j) base b ⟶ Vertex base b :=
  TopCat.ofHom ⟨fun z ↦ ⟨(j z.val.1, z.val.2), z.property⟩, by fun_prop⟩

@[simp] theorem leftLeg_val (z : Source (i := i) (g := g) base b) :
    (leftLeg base b z).val = (i z.val.1, z.val.2) := rfl
@[simp] theorem rightLeg_val (z : Source (i := i) (g := g) base b) :
    (rightLeg sq base b z).val = (f z.val.1, z.val.2) := rfl
@[simp] theorem leftInclusion_val (z : Left (g := g) base b) :
    (leftInclusion base b z).val = (g z.val.1, z.val.2) := rfl
@[simp] theorem rightInclusion_val (z : Right (j := j) base b) :
    (rightInclusion base b z).val = (j z.val.1, z.val.2) := rfl

theorem square : leftLeg base b ≫ leftInclusion base b =
    rightLeg sq base b ≫ rightInclusion base b := by
  ext z : 1
  exact Subtype.ext (Prod.ext (ConcreteCategory.congr_hom sq.w z.val.1) rfl)

include sq in
/-- The actual matched outgoing legs retain the quotient topology. -/
theorem sum_isQuotientMap [LocallyCompactSpace D]
    (hc : IsClosed (Set.ofPred (fun z : P × D ↦ base z.1 = b z.2))) :
    IsQuotientMap (Sum.elim (leftInclusion (g := g) base b) (rightInclusion (j := j) base b)) := by
  let Q := {z : (B ⊕ C) × D // base (Sum.elim g j z.1) = b z.2}
  let pred : (B × D) ⊕ (C × D) → Prop :=
    Sum.elim (fun z ↦ base (g z.1) = b z.2) (fun z ↦ base (j z.1) = b z.2)
  let e : C(Q, {z // pred z}) := {
    toFun z := ⟨Homeomorph.sumProdDistrib z.val, by
      rcases z with ⟨⟨z | z, d⟩, h⟩ <;> exact h⟩
    continuous_toFun := by dsimp only [Q]; fun_prop }
  let split : C(Q, Left (g := g) base b ⊕ Right (j := j) base b) :=
    ⟨fun z ↦ sumSubtypeHomeomorph pred (e z),
      (sumSubtypeHomeomorph pred).continuous.comp e.continuous⟩
  have heq : Sum.elim (leftInclusion (g := g) base b) (rightInclusion (j := j) base b) ∘ split =
      (fun z : Q ↦ (⟨(Sum.elim g j z.val.1, z.val.2), z.property⟩ : Vertex base b)) := by
    funext z
    rcases z with ⟨⟨z | z, d⟩, h⟩ <;> rfl
  exact IsQuotientMap.of_comp split.continuous
    ((leftInclusion base b).hom.continuous.sumElim (rightInclusion base b).hom.continuous)
    (heq.symm ▸ pushout_parameter_pullback_quotient_of_isClosed sq base b hc)

section Desc
variable {Z : TopCat.{u}} (l : Left (g := g) base b ⟶ Z) (r : Right (j := j) base b ⟶ Z)
  (w : leftLeg base b ≫ l = rightLeg sq base b ≫ r)

/-- For a fixed test parameter, extend `l` to an option-valued function on `B`, with value `none`
where the matching equality fails. -/
def leftOption (d : D) (x : B) : Option Z := by
  classical
  exact if hx : base (g x) = b d then some (l ⟨(x, d), hx⟩) else none
/-- For a fixed test parameter, extend `r` to an option-valued function on `C`, with value `none`
where the matching equality fails. -/
def rightOption (d : D) (x : C) : Option Z := by
  classical
  exact if hx : base (j x) = b d then some (r ⟨(x, d), hx⟩) else none

include w in
/-- At each test parameter, the given matching corner maps agree on the
attaching space as option-valued functions, without a nonempty-target premise. -/
theorem option_square (d : D) :
    (forget TopCat).map i ≫ (↾(leftOption base b l d) : (forget TopCat).obj B ⟶ Option Z) =
      (forget TopCat).map f ≫ (↾(rightOption base b r d) : (forget TopCat).obj C ⟶ Option Z) := by
  classical
  apply ConcreteCategory.hom_ext
  intro a
  have he := congrArg base (ConcreteCategory.congr_hom sq.w a)
  change base (g (i a)) = base (j (f a)) at he
  change leftOption base b l d (i a) = rightOption base b r d (f a)
  by_cases ha : base (g (i a)) = b d
  · have ha' : base (j (f a)) = b d := he.symm.trans ha
    simp only [leftOption, rightOption, dite_eq_left ha, dite_eq_left ha']
    exact congrArg some (ConcreteCategory.congr_hom w ⟨(a, d), ha⟩)
  · have ha' : ¬ base (j (f a)) = b d := fun h ↦ ha (he.trans h)
    simp [leftOption, rightOption, ha, ha']

/-- For each test parameter, descend the compatible option-valued corner maps through the
underlying pushout of sets. -/
def optionDesc (d : D) : P → Option Z :=
  (sq.map (forget TopCat)).desc (↾(leftOption base b l d)) (↾(rightOption base b r d))
    (Quillen.CompactParameterPushout.option_square sq base b l r w d)

private theorem optionDesc_left (d : D) (x : B) :
    optionDesc sq base b l r w d (g x) = leftOption base b l d x :=
  ConcreteCategory.congr_hom ((sq.map (forget TopCat)).inl_desc _ _ _) x
private theorem optionDesc_right (d : D) (x : C) :
    optionDesc sq base b l r w d (j x) = rightOption base b r d x :=
  ConcreteCategory.congr_hom ((sq.map (forget TopCat)).inr_desc _ _ _) x

theorem optionDesc_some (z : Vertex base b) :
    ∃ v : Z, optionDesc sq base b l r w z.val.2 z.val.1 = some v := by
  classical
  rcases Types.eq_or_eq_of_isPushout (sq.map (forget TopCat)) z.val.1 with ⟨x, hx⟩ | ⟨x, hx⟩
  · change g x = z.val.1 at hx
    have h : base (g x) = b z.val.2 := (congrArg base hx).trans z.property
    refine ⟨l ⟨(x, z.val.2), h⟩, ?_⟩
    rw [← hx, optionDesc_left]
    simp [leftOption, h]
  · change j x = z.val.1 at hx
    have h : base (j x) = b z.val.2 := (congrArg base hx).trans z.property
    refine ⟨r ⟨(x, z.val.2), h⟩, ?_⟩
    rw [← hx, optionDesc_right]
    simp [rightOption, h]

/-- The descent function on the matched vertex, selecting the value furnished by the
option-valued descent at each matched pair. -/
def descFun (z : Vertex base b) : Z := (optionDesc_some sq base b l r w z).choose

private theorem descFun_left (z : Left (g := g) base b) :
    descFun sq base b l r w (leftInclusion base b z) = l z := by
  classical
  have h := (optionDesc_some sq base b l r w (leftInclusion base b z)).choose_spec
  change optionDesc sq base b l r w z.val.2 (g z.val.1) =
    some (descFun sq base b l r w (leftInclusion base b z)) at h
  rw [optionDesc_left] at h
  simpa [leftOption, z.property] using h.symm

private theorem descFun_right (z : Right (j := j) base b) :
    descFun sq base b l r w (rightInclusion base b z) = r z := by
  classical
  have h := (optionDesc_some sq base b l r w (rightInclusion base b z)).choose_spec
  change optionDesc sq base b l r w z.val.2 (j z.val.1) =
    some (descFun sq base b l r w (rightInclusion base b z)) at h
  rw [optionDesc_right] at h
  simpa [rightOption, z.property] using h.symm

/-- The actual matched cocone descendant, with no nonempty-target assumption. -/
def desc [LocallyCompactSpace D]
    (hc : IsClosed (Set.ofPred (fun z : P × D ↦ base z.1 = b z.2))) : Vertex base b ⟶ Z :=
  TopCat.ofHom ⟨descFun sq base b l r w, by
    apply (sum_isQuotientMap sq base b hc).continuous_iff.2
    have heq : descFun sq base b l r w ∘ Sum.elim (leftInclusion base b) (rightInclusion base b) =
        Sum.elim l r := by
      funext z
      cases z with
      | inl z => exact descFun_left sq base b l r w z
      | inr z => exact descFun_right sq base b l r w z
    rw [heq]
    exact l.hom.continuous.sumElim r.hom.continuous⟩

@[reassoc (attr := simp)] theorem left_desc [LocallyCompactSpace D]
    (hc : IsClosed (Set.ofPred (fun z : P × D ↦ base z.1 = b z.2))) :
    leftInclusion base b ≫ desc sq base b l r w hc = l := by
  ext z : 1
  exact descFun_left sq base b l r w z
@[reassoc (attr := simp)] theorem right_desc [LocallyCompactSpace D]
    (hc : IsClosed (Set.ofPred (fun z : P × D ↦ base z.1 = b z.2))) :
    rightInclusion base b ≫ desc sq base b l r w hc = r := by
  ext z : 1
  exact descFun_right sq base b l r w z
end Desc

/-- A genuine pushout square on the literal matched objects. The locally
compact parameter and closed matching locus are retained explicitly. -/
theorem isPushout [LocallyCompactSpace D]
    (hc : IsClosed (Set.ofPred (fun z : P × D ↦ base z.1 = b z.2))) :
    IsPushout (leftLeg base b) (rightLeg sq base b) (leftInclusion base b) (rightInclusion base
      b) := by
  apply IsPushout.of_isColimit (c := PushoutCocone.mk _ _ (square sq base b))
  refine PushoutCocone.IsColimit.mk _ (fun s ↦ desc sq base b s.inl s.inr s.condition hc)
    (fun s ↦ left_desc sq base b s.inl s.inr s.condition hc)
    (fun s ↦ right_desc sq base b s.inl s.inr s.condition hc) ?_
  intro s m hm₁ hm₂
  ext z : 1
  obtain ⟨z, rfl⟩ := (sum_isQuotientMap sq base b hc).surjective z
  cases z with
  | inl z =>
      exact (ConcreteCategory.congr_hom hm₁ z).trans
        (ConcreteCategory.congr_hom (left_desc sq base b s.inl s.inr s.condition hc) z).symm
  | inr z =>
      exact (ConcreteCategory.congr_hom hm₂ z).trans
        (ConcreteCategory.congr_hom (right_desc sq base b s.inl s.inr s.condition hc) z).symm

/-- Closed graph is a separate sufficient condition; no global separation
condition on the base is substituted for it. -/
theorem isPushout_of_closedGraph [LocallyCompactSpace D]
    (hb : IsClosed (Set.ofPred (fun z : D × T ↦ b z.1 = z.2))) :
    IsPushout (leftLeg base b) (rightLeg sq base b) (leftInclusion base b) (rightInclusion base
      b) := by
  apply isPushout sq base b
  convert hb.preimage (continuous_snd.prodMk (base.continuous.comp continuous_fst)) using 1
  ext z
  exact eq_comm

/-- Actual simplicial realizations supply the closed locus for compact tests. -/
theorem isPushout_realization (X : SSet.{u}) [CompactSpace D] [LocallyCompactSpace D]
    (p : C(P, |X|)) (t : C(D, |X|)) :
    IsPushout (leftLeg p t) (rightLeg sq p t) (leftInclusion p t) (rightInclusion p t) :=
  isPushout sq p t (realization_compactMap_matching_isClosed X p t)

/-- The unchanged displayed double-cylinder realization model supplies the
same genuine finite-parameter pushout square. -/
theorem isPushout_doubleCylinder {X Y Z : SSet.{u}} (f₀ : X ⟶ Y) (g₀ : X ⟶ Z)
    {l₀ : |X| ⊗ TopCat.I ⟶ T} {e₀ : TopCat.of (|Y| ⊕ |Z|) ⟶ T}
    (sqT : IsPushout (Quillen.intervalEndpoints |X|)
      (DoubleCylinder.endMap (SSet.toTop.map f₀) (SSet.toTop.map g₀)) l₀ e₀)
    [CompactSpace D] [LocallyCompactSpace D] :
    IsPushout (leftLeg base b) (rightLeg sq base b) (leftInclusion base b) (rightInclusion base
      b) :=
  isPushout sq base b (DoubleCylinder.compactMap_matching_isClosed f₀ g₀ sqT base b)

end Quillen.CompactParameterPushout
