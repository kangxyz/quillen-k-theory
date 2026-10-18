/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedSections

/-!
# Actual supported global sections and coefficient restriction

Support is acyclicity after original evaluation and restriction to the specified open.
The actual coefficient restriction preserves this predicate, and its forgetful and evaluated
squares are equalities of the original functors.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.Complex
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

private theorem liftSquare {A B C D : Type*}
    [Category* A] [Category* B] [Category* C] [Category* D]
    (P : ObjectProperty A) (Q : ObjectProperty B) (T : ObjectProperty D)
    (F : A ⥤ B) (G : B ⥤ C) (E : A ⥤ C) (I : C ⥤ D) (h : F ⋙ G = E)
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    (hG : ∀ X : Q.FullSubcategory, T (I.obj (G.obj X.obj)))
    (hE : ∀ X : P.FullSubcategory, T (I.obj (E.obj X.obj))) :
    Q.lift (P.ι ⋙ F) hF ⋙ T.lift (Q.ι ⋙ G ⋙ I) hG =
      T.lift (P.ι ⋙ E ⋙ I) hE := by
  change T.lift (P.ι ⋙ F ⋙ G ⋙ I) _ = _
  apply supported_lift_congr
  rw [← Functor.assoc F, h]

/-- A global section is supported precisely when its restriction is acyclic. -/
def supported {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} (j : U ⟶ X.unop)
    [IsOpenImmersion j] : ObjectProperty (globalModel.obj X) := fun S =>
  ((restrict j).obj ((globalEvaluation X).obj S).obj).Acyclic

/-- Original evaluation on the full subcategory of supported global sections. -/
def supportedEvaluation {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} (j : U ⟶ X.unop)
    [IsOpenImmersion j] :
    (supported j).FullSubcategory ⥤ (boundedFlatPerfectSupported j).FullSubcategory :=
  (boundedFlatPerfectSupported j).lift
    ((supported j).ι ⋙ globalEvaluation X ⋙ (boundedFlatPerfect X.unop).ι)
    (fun S => ⟨((globalEvaluation X).obj S.obj).property, S.property⟩)

/-- Geometric support is the inverse image of its original evaluated predicate. -/
theorem supported_property {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}} (j : U ⟶ X.unop)
    [IsOpenImmersion j] :
    ((boundedFlatPerfectSupported j).inverseImage (boundedFlatPerfect X.unop).ι).inverseImage
      (globalEvaluation X).asEquivalence.functor = supported j := by
  funext S
  apply propext
  exact and_iff_right ((globalEvaluation X).obj S).property

instance supportedEvaluation_isEquivalence {X : Scheme.{u}ᵒᵖ} {U : Scheme.{u}}
    (j : U ⟶ X.unop) [IsOpenImmersion j] : (supportedEvaluation j).IsEquivalence := by
  let e := Quillen.ObjectProperty.evaluationRestrictionEquivalence
    (boundedFlatPerfect X.unop) (boundedFlatPerfectSupported j) (fun _ h => h.1)
    (globalEvaluation X).asEquivalence (supported j) (supported_property j)
  have he : e.functor = supportedEvaluation j := rfl
  rw [← he]
  exact e.isEquivalence_functor

variable (R : CommRingCat.{u}) (c : Index R) {U : Scheme.{u}}
    (j : U ⟶ space c) [IsOpenImmersion j]

/-- The original coefficient restriction preserves the exact acyclicity predicate. -/
theorem restriction_supported (S : globalModel.obj
    ((AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c)) :
    boundedFlatCoefficientSectionSupported j (((coefficientRestriction R).app c).functor.obj S) ↔
      supported (X := (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j S := by
  have h := congrArg (fun F => F.obj S) (coefficientRestriction_evaluation R c)
  exact Iff.of_eq (congrArg (fun K : BoundedFlatPerfect (space c) =>
    ((restrict j).obj K.obj).Acyclic) h)

/-- Restrict actual supported global sections to original coefficient sections. -/
def supportedRestriction :
    (supported (X := (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c)
      j).FullSubcategory ⥤
    BoundedFlatCoefficientSupportedSections j :=
  (boundedFlatCoefficientSectionSupported j).lift
    ((supported (X := (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j).ι ⋙
      ((coefficientRestriction R).app c).functor)
    (fun S => (restriction_supported R c j S.obj).mpr S.property)

/-- The support-forgetful square retains every original section and morphism. -/
theorem supportedRestriction_forget :
    supportedRestriction R c j ⋙ (boundedFlatCoefficientSectionSupported j).ι =
      (supported (X := (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j).ι ⋙
        ((coefficientRestriction R).app c).functor := rfl

/-- The supported evaluation square is literal equality of full functors. -/
theorem supportedRestriction_evaluation :
    supportedRestriction R c j ⋙ boundedFlatCoefficientSupportedEvaluation j =
      supportedEvaluation
        (X := (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) j := by
  exact liftSquare _ _ _ ((coefficientRestriction R).app c).functor
    (boundedFlatCoefficientOriginalEvaluation c) (globalEvaluation _)
    (boundedFlatPerfect (space c)).ι (coefficientRestriction_evaluation R c) _ _ _

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
