/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionLaurentUnit

/-!
# Evaluation compares the strict Laurent pullback action with the original geometric action

The original coordinate inclusion gives the actual strict section reindexing functor. Its unit
action is the same original Laurent unit. The original evaluation transition intertwines it with
bounded-flat geometric Laurent pullback and the already existing original unit automorphism.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable (R : CommRingCat.{u})

/-- The strict Laurent pullback carries the original section coordinate-unit action. -/
def boundedFlatAffineSectionLaurentPullbackUnitIso :
    boundedFlatAffineSectionsMap (CommRingCat.ofHom (LaurentPolynomial.C (R := R))) ≅
      boundedFlatAffineSectionsMap (CommRingCat.ofHom (LaurentPolynomial.C (R := R))) :=
  Quillen.FunctorIdentityAutomorphism.onFunctor
    (boundedFlatAffineSectionsMap (CommRingCat.ofHom LaurentPolynomial.C))
    (boundedFlatAffineSectionLaurentUnitIso R)

/-- The actual evaluation transition compares strict Laurent reindexing with original pullback. -/
def boundedFlatAffineSectionLaurentEvaluationIso :
    boundedFlatAffineOriginalEvaluation R ⋙ boundedFlatPerfectPullback (laurentProjection R) ≅
      boundedFlatAffineSectionsMap (CommRingCat.ofHom LaurentPolynomial.C) ⋙
        boundedFlatAffineOriginalEvaluation (.of (LaurentPolynomial R)) :=
  boundedFlatAffineEvaluationPullbackIso R (Under.mk (CommRingCat.ofHom LaurentPolynomial.C)) ≪≫
    eqToIso (boundedFlatAffineSectionsMap_comp_evaluation
      (CommRingCat.ofHom LaurentPolynomial.C)).symm

private theorem sectionLaurentPullbackUnitIso_eq :
    boundedFlatAffineSectionLaurentPullbackUnitIso R =
      Quillen.FunctorIdentityAutomorphism.onFunctor
        (boundedFlatAffineSectionsMap (CommRingCat.ofHom LaurentPolynomial.C))
        (boundedFlatAffineSectionLaurentUnitIso R) := rfl

private theorem sectionLaurentUnitIso_eq :
    boundedFlatAffineSectionLaurentUnitIso R =
      boundedFlatAffineSectionUnitIso (.of (LaurentPolynomial R)) (laurentGlobalUnit R) := rfl

/-- Original evaluation intertwines the actual strict and geometric Laurent-unit actions. -/
theorem boundedFlatAffineSectionLaurentPullbackUnitIso_evaluation :
    Functor.whiskerLeft (boundedFlatAffineOriginalEvaluation R)
        (boundedFlatPerfectPullbackUnitIso (laurentProjection R) (laurentGlobalUnit R)).hom ≫
      (boundedFlatAffineSectionLaurentEvaluationIso R).hom =
    (boundedFlatAffineSectionLaurentEvaluationIso R).hom ≫
      Functor.whiskerRight (boundedFlatAffineSectionLaurentPullbackUnitIso R).hom
        (boundedFlatAffineOriginalEvaluation (.of (LaurentPolynomial R))) := by
  rw [sectionLaurentPullbackUnitIso_eq, sectionLaurentUnitIso_eq,
    boundedFlatPerfectPullbackUnitIso, Quillen.FunctorIdentityAutomorphism.onFunctor_comp_hom]
  exact Quillen.FunctorIdentityAutomorphism.onFunctor_intertwine
    (boundedFlatAffineOriginalEvaluation R ⋙ boundedFlatPerfectPullback (laurentProjection R))
    (boundedFlatAffineSectionsMap (CommRingCat.ofHom LaurentPolynomial.C))
    (boundedFlatAffineOriginalEvaluation (.of (LaurentPolynomial R)))
    (boundedFlatAffineSectionLaurentEvaluationIso R).hom
    (boundedFlatAffineSectionUnitIso (.of (LaurentPolynomial R)) (laurentGlobalUnit R))
    (boundedFlatPerfectGlobalUnitIso (Spec (.of (LaurentPolynomial R))) (laurentGlobalUnit R))
    (boundedFlatAffineOriginalEvaluation_map_sectionUnitIso_hom
      (.of (LaurentPolynomial R)) (laurentGlobalUnit R))

end Quillen.PerfectComplexes
