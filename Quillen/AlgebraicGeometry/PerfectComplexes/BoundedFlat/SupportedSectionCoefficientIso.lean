/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSections
public import Quillen.CategoryTheory.ObjectProperty.LiftComposition

/-!
# Original geometric coefficient comparison with support retained

The same original cocartesian coefficient transition is lifted through the actual fully faithful
supported inclusion. The named forget identities and their literal object-identity transports
remain explicit. This is a natural isomorphism, not a strict naturality equation for geometric
evaluation. Expanding its components is a separate projection calculation.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)
attribute [local irreducible] boundedFlatAffineOriginalEvaluation boundedFlatAffineEvaluationAt

/-- The original specified affine open square, with its unchanged coefficient and open maps. -/
def boundedFlatAffineSupportedPairSquare :
    (⟨Arrow.mk j', (show IsOpenImmersion j' from inferInstance)⟩ :
      AlgebraicGeometry.Scheme.OpenPairs) ⟶
      ⟨Arrow.mk j, (show IsOpenImmersion j from inferInstance)⟩ :=
  ObjectProperty.homMk (Arrow.homMk l (Spec.map f) h)

/-- Forgetting the supported evaluation retains the original complex-valued functor. -/
theorem boundedFlatAffineSupportedEvaluation_forget :
    boundedFlatAffineSupportedEvaluation j ⋙ (boundedFlatPerfectSupported j).ι =
      (boundedFlatAffineSectionSupported j).ι ⋙ boundedFlatAffineOriginalEvaluation R ⋙
        (boundedFlatPerfect (Spec R)).ι :=
  Quillen.ObjectProperty.lift_comp_ι (boundedFlatPerfectSupported j)
    ((boundedFlatAffineSectionSupported j).ι ⋙ boundedFlatAffineOriginalEvaluation R ⋙
      (boundedFlatPerfect (Spec R)).ι)
    (fun s ↦ ⟨((boundedFlatAffineOriginalEvaluation R).obj s.obj).property, s.property⟩)

section
attribute [local irreducible] boundedFlatAffineSupportedSectionsMap
  boundedFlatAffineSupportedEvaluation

/-- Forgetting support after original reindexing and evaluation keeps that actual composite. -/
theorem boundedFlatAffineSupportedReindexEvaluation_forget :
    (boundedFlatAffineSupportedSectionsMap j j' f l h ⋙
        boundedFlatAffineSupportedEvaluation j') ⋙ (boundedFlatPerfectSupported j').ι =
      (boundedFlatAffineSectionSupported j).ι ⋙
        (boundedFlatAffineSectionsMap f ⋙ boundedFlatAffineOriginalEvaluation S) ⋙
          (boundedFlatPerfect (Spec S)).ι :=
  Quillen.ObjectProperty.comp_forget_eq
    (boundedFlatAffineSectionSupported j) (boundedFlatAffineSectionSupported j')
    (boundedFlatPerfectSupported j')
    (boundedFlatAffineSupportedSectionsMap j j' f l h) (boundedFlatAffineSupportedEvaluation j')
    (boundedFlatAffineSectionsMap f) (boundedFlatAffineOriginalEvaluation S)
    (boundedFlatPerfect (Spec S)).ι
    (boundedFlatAffineSupportedSectionsMap_forget j j' f l h)
    (boundedFlatAffineSupportedEvaluation_forget j')
end

/-- Original supported geometric pullback retains the literal complex pullback after forgetting. -/
theorem boundedFlatAffineSupportedPairPullback_forget :
    boundedFlatPerfectSupportedPullback (boundedFlatAffineSupportedPairSquare j j' f l h) ⋙
        (boundedFlatPerfectSupported j').ι =
      (boundedFlatPerfectSupported j).ι ⋙ pullbackComplex (Spec.map f) :=
  Quillen.ObjectProperty.lift_comp_ι (boundedFlatPerfectSupported j')
    ((boundedFlatPerfectSupported j).ι ⋙ pullbackComplex (Spec.map f))
    (fun K ↦ boundedFlatPerfectSupported_pairPullback
      (boundedFlatAffineSupportedPairSquare j j' f l h) K.property)
/-- The original bounded-flat pullback forgets to the exact original complex pullback. -/
theorem boundedFlatAffineOriginalPullback_forget :
    boundedFlatPerfectPullback (Spec.map f) ⋙ (boundedFlatPerfect (Spec S)).ι =
      (boundedFlatPerfect (Spec R)).ι ⋙ pullbackComplex (Spec.map f) :=
  Quillen.ObjectProperty.lift_comp_ι (boundedFlatPerfect (Spec S))
    ((boundedFlatPerfect (Spec R)).ι ⋙ pullbackComplex (Spec.map f))
    (fun K ↦ boundedFlatPerfect_pullback (Spec.map f) K.property)

section
attribute [local irreducible] boundedFlatAffineSupportedEvaluation
  boundedFlatPerfectSupportedPullback boundedFlatPerfectPullback
/-- The original evaluation/pair-pullback composite retains its specified underlying functor. -/
theorem boundedFlatAffineSupportedEvaluationPullback_forget :
    (boundedFlatAffineSupportedEvaluation j ⋙
        boundedFlatPerfectSupportedPullback (boundedFlatAffineSupportedPairSquare j j' f l h)) ⋙
        (boundedFlatPerfectSupported j').ι =
      (boundedFlatAffineSectionSupported j).ι ⋙
        (boundedFlatAffineOriginalEvaluation R ⋙ boundedFlatPerfectPullback (Spec.map f)) ⋙
          (boundedFlatPerfect (Spec S)).ι :=
  Quillen.ObjectProperty.comp_forget_eq_of_comparison
    (boundedFlatAffineSectionSupported j) (boundedFlatPerfectSupported j)
    (boundedFlatPerfectSupported j') (boundedFlatAffineSupportedEvaluation j)
    (boundedFlatPerfectSupportedPullback (boundedFlatAffineSupportedPairSquare j j' f l h))
    (boundedFlatAffineOriginalEvaluation R) (boundedFlatPerfect (Spec R)).ι
    (pullbackComplex (Spec.map f)) (boundedFlatPerfectPullback (Spec.map f))
    (boundedFlatPerfect (Spec S)).ι (boundedFlatAffineSupportedEvaluation_forget j)
    (boundedFlatAffineSupportedPairPullback_forget j j' f l h)
    (boundedFlatAffineOriginalPullback_forget f)

/-- The original coefficient transition restricts to a genuine supported natural isomorphism. -/
def boundedFlatAffineSupportedSectionCoefficientIso :
    boundedFlatAffineSupportedSectionsMap j j' f l h ⋙ boundedFlatAffineSupportedEvaluation j' ≅
      boundedFlatAffineSupportedEvaluation j ⋙
        boundedFlatPerfectSupportedPullback (boundedFlatAffineSupportedPairSquare j j' f l h) :=
  Quillen.ObjectProperty.isoOfForgetIso (boundedFlatPerfectSupported j')
    (boundedFlatAffineSupportedSectionsMap j j' f l h ⋙ boundedFlatAffineSupportedEvaluation j')
    (boundedFlatAffineSupportedEvaluation j ⋙
      boundedFlatPerfectSupportedPullback (boundedFlatAffineSupportedPairSquare j j' f l h))
    _ _ (boundedFlatAffineSupportedReindexEvaluation_forget j j' f l h)
    (boundedFlatAffineSupportedEvaluationPullback_forget j j' f l h)
    (Functor.isoWhiskerLeft (boundedFlatAffineSectionSupported j).ι
      (Functor.isoWhiskerRight
        (eqToIso (boundedFlatAffineSectionsMap_comp_evaluation f) ≪≫
          (boundedFlatAffineEvaluationPullbackIso R (Under.mk f)).symm)
        (boundedFlatPerfect (Spec S)).ι))
end

/-- The left forget identity is literally identity on every original evaluated complex. -/
theorem boundedFlatAffineSupportedReindexEvaluation_forget_eqToHom
    (s : BoundedFlatAffineSupportedSections j) :
    eqToHom (congrArg (fun K : BoundedFlatAffineSupportedSections j ⥤ Complex (Spec S) ↦ K.obj s)
      (boundedFlatAffineSupportedReindexEvaluation_forget j j' f l h)) =
      𝟙 (((boundedFlatAffineOriginalEvaluation S).obj
        ((boundedFlatAffineSectionsMap f).obj s.obj)).obj) := rfl
/-- The inverse right forget identity is identity on the original pulled-back complex. -/
theorem boundedFlatAffineSupportedEvaluationPullback_forget_eqToHom
    (s : BoundedFlatAffineSupportedSections j) :
    eqToHom (congrArg (fun K : BoundedFlatAffineSupportedSections j ⥤ Complex (Spec S) ↦ K.obj s)
      (boundedFlatAffineSupportedEvaluationPullback_forget j j' f l h).symm) =
      𝟙 (((boundedFlatPerfectPullback (Spec.map f)).obj
        ((boundedFlatAffineOriginalEvaluation R).obj s.obj)).obj) := rfl

end Quillen.PerfectComplexes
