/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionLaurentChangeWeak
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionBassSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassSeed

/-!
# The original full-open Bass seed commutes with quotient grading

The actual fine-to-coarse natural transformation supplies the four-corner Laurent square and
unchanged cone map. Its original null cylinder and whole scalar track prove compatibility of
the two genuinely constructed seeds. The source is the accepted actual full-open seed.
The target is its genuinely constructed quotient-graded counterpart. No seed square,
localization, or contraction is assumed.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The original four fine-to-coarse maps give the actual Laurent-square map. -/
def boundedFlatAffineFullOpenSectionBassSquareChangeWeak (a : Under R) :
    boundedFlatAffineFullOpenSectionBassSquare j a ⟶
      boundedFlatAffineFullOpenGradedSectionBassSquare j a :=
  ((Functor.mapArrowFunctor (Arrow (Under R)) (Arrow LoopPrespectrum.{u + 1})).map
    ((Functor.mapArrowFunctor (Under R) LoopPrespectrum.{u + 1}).map
      (boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j))).app
        (laurentUnderSquare R a)

/-- The original cone functor acts on that same four-corner map. -/
def boundedFlatAffineFullOpenSectionBassConeChangeWeak (a : Under R) :
    boundedFlatAffineFullOpenSectionBassCone j a ⟶
      boundedFlatAffineFullOpenGradedSectionBassCone j a :=
  mappingConeMap (strictSquareComparisonFunctor.map
    (boundedFlatAffineFullOpenSectionBassSquareChangeWeak j a))

/-- The whole original source-leg null cylinder survives at the identical time. -/
theorem boundedFlatAffineFullOpenSectionBassNullHomotopy_changeWeak_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineFullOpenSectionPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineFullOpenSectionBassConeChangeWeak j a).map n
        ((boundedFlatAffineFullOpenSectionBassNullHomotopy j a).level n (t, x)) =
      (boundedFlatAffineFullOpenGradedSectionBassNullHomotopy j a).level n
        (t, ((boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j).app a).map n x) :=
  StrictSquare.sourceNullHomotopy_naturality_apply
    (boundedFlatAffineFullOpenSectionBassSquareChangeWeak j a) n t x

/-- The two constructed seed maps commute with the original change of section weaknesses. -/
theorem boundedFlatAffineFullOpenSectionBassSeedMap_changeWeak (a : Under R) :
    boundedFlatAffineFullOpenSectionBassSeedMap j a ≫
        parameterLoopingMap (boundedFlatAffineFullOpenSectionBassConeChangeWeak j a) =
      (boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j).app a ≫
        boundedFlatAffineFullOpenGradedSectionBassSeedMap j a := by
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    change (mappingConeInclusion
      (StrictSquare.comparison (boundedFlatAffineFullOpenGradedSectionBassSquare j a))).map n
        (((boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j).app
          ((laurentUnderFunctor R).obj a)).map n
          ((boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy j a).level n (t, x))) =
      (mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineFullOpenGradedSectionBassSquare j a))).map n
          ((boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a).level n
            (t, ((boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j).app a).map n
              x))
    rw [boundedFlatAffineFullOpenSectionDiagramLaurentHomotopy_changeWeak_apply]
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact boundedFlatAffineFullOpenSectionBassNullHomotopy_changeWeak_apply j a n t x

section
attribute [local irreducible] boundedFlatAffineFullOpenSectionPrespectrumFunctor
  boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor
  boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation

/-- The unchanged Bass functor acts by this exact looped fine-to-coarse cone map. -/
theorem boundedFlatAffineFullOpenSectionBassChangeWeak_functor_app (a : Under R) :
    ((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j)).app a =
      parameterLoopingMap (boundedFlatAffineFullOpenSectionBassConeChangeWeak j a) := rfl

end

attribute [local irreducible] boundedFlatAffineFullOpenSectionPrespectrumFunctor
  boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor
  boundedFlatAffineFullOpenGradedSectionBassSeed boundedFlatAffineFullOpenSectionBassSeed
  boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation

/-- The strict fine-to-coarse natural arrow preserves the exact original seed transformations. -/
theorem boundedFlatAffineFullOpenSectionBassSeed_changeWeak :
    boundedFlatAffineFullOpenSectionBassSeed j ≫
        (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j) =
      boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j ≫
        boundedFlatAffineFullOpenGradedSectionBassSeed j := by
  apply NatTrans.ext
  funext a
  simp only [NatTrans.comp_app, boundedFlatAffineFullOpenGradedSectionBassSeed_app,
    boundedFlatAffineFullOpenSectionBassChangeWeak_functor_app,
    boundedFlatAffineFullOpenSectionBassSeed_app]
  exact boundedFlatAffineFullOpenSectionBassSeedMap_changeWeak j a

end Quillen.PerfectComplexes
