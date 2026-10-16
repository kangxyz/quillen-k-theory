/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.SectionFullOpenRestriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.SectionEvaluation

/-!
# Original full-open coefficient comparison for coarse section evaluation

The isomorphism is the original section transition followed by the original open-pair
pullback comparison, with precisely the associators of the unchanged composite functor.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatAffineOriginalEvaluation

/-- The original coefficient transition followed by the original open-pair comparison. -/
def boundedFlatAffineSectionFullOpenCoefficientIso {a b : Under R} (f : a ⟶ b) :
    boundedFlatAffineSectionsMap f.right ⋙ boundedFlatAffineSectionFullOpenRestriction j b ≅
      boundedFlatAffineSectionFullOpenRestriction j a ⋙
        boundedFlatPerfectPullback (openMap j f) :=
  (Functor.associator (boundedFlatAffineSectionsMap f.right)
    (boundedFlatAffineOriginalEvaluation b.right)
    (boundedFlatAffineFullOpenRestriction j b)).symm ≪≫
  Functor.isoWhiskerRight
    (eqToIso (boundedFlatAffineSectionsMap_comp_evaluation f.right) ≪≫
      (boundedFlatAffineEvaluationPullbackIso a.right (Under.mk f.right)).symm)
    (boundedFlatAffineFullOpenRestriction j b) ≪≫
  Functor.associator (boundedFlatAffineOriginalEvaluation a.right)
    (boundedFlatPerfectPullback (Spec.map f.right))
    (boundedFlatAffineFullOpenRestriction j b) ≪≫
  Functor.isoWhiskerLeft (boundedFlatAffineOriginalEvaluation a.right)
    (boundedFlatAffineFullOpenRestrictionIso j f) ≪≫
  (Functor.associator (boundedFlatAffineOriginalEvaluation a.right)
    (boundedFlatAffineFullOpenRestriction j a)
    (boundedFlatPerfectPullback (openMap j f))).symm

end Quillen.PerfectComplexes
