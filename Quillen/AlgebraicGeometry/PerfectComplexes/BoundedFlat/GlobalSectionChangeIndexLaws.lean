/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionChangeIndex

/-!
# Actual evaluation and finite stability for global-to-coefficient sections

These laws concern the original coefficient base-product restriction, landing in the existing
coefficient-first Models. Exactness of a categorical inverse suffices for stable equivalence.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass Quillen.LoopPrespectrum
open CategoryTheory.SectionChangeIndex
open Quillen.CategoryTheory.GrothendieckSections
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.GlobalSectionChangeIndex

/-- The underlying functor is the original restriction along `Under.post` of base product. -/
theorem coefficientRestriction_functor (R : CommRingCat.{u}) (c : Index R) :
    ((coefficientRestriction R).app c).functor =
      underFunctor boundedFlatPerfectPseudofunctor
        (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R) c := rfl

/-- Identity evaluation after actual restriction is literally original global evaluation. -/
theorem coefficientRestriction_evaluation (R : CommRingCat.{u}) (c : Index R) :
    ((coefficientRestriction R).app c).functor ⋙ boundedFlatCoefficientOriginalEvaluation c =
      originalEvaluation boundedFlatPerfectPseudofunctor
        ((AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c) :=
  evaluation boundedFlatPerfectPseudofunctor
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R) c

/-- Actual restriction is a categorical equivalence. -/
instance coefficientRestriction_isEquivalence (R : CommRingCat.{u}) (c : Index R) :
    ((coefficientRestriction R).app c).functor.IsEquivalence :=
  restriction_isEquivalence boundedFlatPerfectPseudofunctor
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R) c

/-- Its categorical inverse is exact for the original evaluation-transported structures. -/
theorem coefficientRestriction_inverse_exact (R : CommRingCat.{u}) (c : Index R) :
    Waldhausen.IsExact (boundedFlatCoefficientSectionModel c).waldhausen.cof
      (boundedFlatCoefficientSectionModel c).waldhausen.weq
      (globalModel.obj
        ((AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c)).waldhausen.cof
      (globalModel.obj
        ((AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj c)).waldhausen.weq
      ((coefficientRestriction R).app c).functor.asEquivalence.inverse :=
  Quillen.Waldhausen.IteratedS.SectionChangeIndexMixedModel.restriction_inverse_exact
    boundedFlatPerfectPseudofunctor fiberWaldhausen fiberZero fiberZero_isZero
    (fun {_ _} f => fiberZero_map_isZero f)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R) c

/-- Every actual finite Bass iterate of this restriction is a stable equivalence. -/
theorem coefficientRestriction_iterate_isStableEquivalence (R : CommRingCat.{u})
    (Q : Index R ⥤ Arrow (Arrow (Index R))) (i : ℕ) (c : Index R) :
    IsStableEquivalence (((strictDiagramIterate Q i).map
      (Functor.whiskerRight (coefficientRestriction R) prespectrumFunctor)).app c) := by
  apply modelDiagramIterate_map_isStableEquivalence_of_exactEquivalence Q i _ _
    (coefficientRestriction R)
    (fun c => ((coefficientRestriction R).app c).functor.asEquivalence) (fun _ => rfl)
  exact fun c => coefficientRestriction_inverse_exact R c

end Quillen.PerfectComplexes.GlobalSectionChangeIndex
