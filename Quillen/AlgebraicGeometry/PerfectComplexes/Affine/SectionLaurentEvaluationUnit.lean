/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.CategoryTheory.Iso.ReverseTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionLaurentPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionSpectrumNaturality

/-!
# The original categorical Laurent-unit evaluation equation

The actual strict section action and geometric Laurent scalar intertwine through the unchanged
coefficient comparison. This owner retains the categorical square used for its whole-track lift.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent
open Quillen.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes

/-- The existing coefficient iso is exactly the original Laurent evaluation iso in reverse. -/
theorem boundedFlatAffineSectionCoefficientIso_laurent (R : CommRingCat.{u}) :
    boundedFlatAffineSectionCoefficientIso (R := R) (S := .of (LaurentPolynomial R))
      (laurentCoefficient R) =
      (boundedFlatAffineSectionLaurentEvaluationIso R).symm :=
  Iso.eqToIso_trans_symm
    (boundedFlatAffineEvaluationPullbackIso R (Under.mk (laurentCoefficient R)))
    (boundedFlatAffineSectionsMap_comp_evaluation
      (R := R) (S := .of (LaurentPolynomial R)) (laurentCoefficient R))

/-- The actual original Laurent unit square has the coefficient track's required orientation. -/
theorem boundedFlatAffineSectionLaurentCoefficientUnitSquare (R : CommRingCat.{u}) :
    whiskerRight (boundedFlatAffineSectionLaurentPullbackUnitIso R).hom
        (boundedFlatAffineOriginalEvaluation (.of (LaurentPolynomial R))) ≫
      (boundedFlatAffineSectionCoefficientIso (R := R) (S := .of (LaurentPolynomial R))
      (laurentCoefficient R)).hom =
    (boundedFlatAffineSectionCoefficientIso (R := R) (S := .of (LaurentPolynomial R))
      (laurentCoefficient R)).hom ≫
      whiskerLeft (boundedFlatAffineOriginalEvaluation R)
        (boundedFlatPerfectPullbackUnitIso (laurentProjection R) (laurentGlobalUnit R)).hom := by
  rw [boundedFlatAffineSectionCoefficientIso_laurent]
  have h := congrArg (fun η => (boundedFlatAffineSectionLaurentEvaluationIso R).inv ≫
    η ≫ (boundedFlatAffineSectionLaurentEvaluationIso R).inv)
      (boundedFlatAffineSectionLaurentPullbackUnitIso_evaluation R)
  simpa only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id] using h.symm

end Quillen.PerfectComplexes
