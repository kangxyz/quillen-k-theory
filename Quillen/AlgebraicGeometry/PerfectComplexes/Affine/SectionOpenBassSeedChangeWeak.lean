/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionOpenLaurentChangeWeak
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionOpenBassSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionForgetSeed

/-!
# The original fine and relative-open Bass seeds commute with change of weaknesses

The actual fine-to-coarse natural transformation supplies the four-corner Laurent square and
unchanged cone map. Its original null cylinder and whole scalar track prove compatibility of
the two genuinely constructed seeds. The source is the already constructed ambient seed
restricted along Under.forget. No seed square, localization or full-open equivalence is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original four fine-to-coarse maps give the actual Laurent-square map. -/
def boundedFlatAffineSectionOpenBassSquareChangeWeak (a : Under R) :
    boundedFlatAffineSectionBassSquare a.right ⟶ boundedFlatAffineSectionOpenBassSquare j a :=
  ((Functor.mapArrowFunctor (Arrow (Under R)) (Arrow LoopPrespectrum.{u+1})).map
    ((Functor.mapArrowFunctor (Under R) LoopPrespectrum.{u+1}).map
      (boundedFlatAffineSectionOpenPrespectrumTransformation j))).app
        (laurentUnderSquare R a)

/-- The original cone functor acts on that same four-corner map. -/
def boundedFlatAffineSectionOpenBassConeChangeWeak (a : Under R) :
    boundedFlatAffineSectionBassCone a.right ⟶ boundedFlatAffineSectionOpenBassCone j a :=
  mappingConeMap (strictSquareComparisonFunctor.map
    (boundedFlatAffineSectionOpenBassSquareChangeWeak j a))

/-- The whole original source-leg null cylinder survives at the identical time. -/
theorem boundedFlatAffineSectionOpenBassNullHomotopy_changeWeak_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : (boundedFlatAffineSectionPrespectrumFunctor.obj a.right).space n) :
    (boundedFlatAffineSectionOpenBassConeChangeWeak j a).map n
        ((boundedFlatAffineSectionBassNullHomotopy a.right).level n (t, x)) =
      (boundedFlatAffineSectionOpenBassNullHomotopy j a).level n
        (t, (boundedFlatAffineSectionOpenPrespectrumMap (inclusion j a)).map n x) :=
  StrictSquare.sourceNullHomotopy_naturality_apply
    (boundedFlatAffineSectionOpenBassSquareChangeWeak j a) n t x

/-- The two constructed seed maps commute with the original change of section weaknesses. -/
theorem boundedFlatAffineSectionOpenBassSeedMap_changeWeak (a : Under R) :
    boundedFlatAffineSectionBassSeedMap a.right ≫
        parameterLoopingMap (boundedFlatAffineSectionOpenBassConeChangeWeak j a) =
      (boundedFlatAffineSectionOpenPrespectrumTransformation j).app a ≫
        boundedFlatAffineSectionOpenBassSeedMap j a := by
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    change (mappingConeInclusion
      (StrictSquare.comparison (boundedFlatAffineSectionOpenBassSquare j a))).map n
        ((boundedFlatAffineSectionOpenPrespectrumMap
          (inclusion j ((laurentUnderFunctor R).obj a))).map n
          ((boundedFlatAffineSectionLaurentUnitHomotopy a.right).level n (t, x))) =
      (mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineSectionOpenBassSquare j a))).map n
          ((boundedFlatAffineSectionOpenDiagramLaurentHomotopy j a).level n
            (t, (boundedFlatAffineSectionOpenPrespectrumMap (inclusion j a)).map n x))
    rw [boundedFlatAffineSectionOpenDiagramLaurentHomotopy_changeWeak_apply]
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact boundedFlatAffineSectionOpenBassNullHomotopy_changeWeak_apply j a n t x

section
attribute [local irreducible] boundedFlatAffineSectionPrespectrumFunctor
  boundedFlatAffineSectionOpenPrespectrumFunctor
  boundedFlatAffineSectionOpenPrespectrumTransformation

/-- The unchanged Bass functor acts by this exact looped fine-to-coarse cone map. -/
theorem boundedFlatAffineSectionOpenBassChangeWeak_functor_app (a : Under R) :
    ((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatAffineSectionOpenPrespectrumTransformation j)).app a =
      parameterLoopingMap (boundedFlatAffineSectionOpenBassConeChangeWeak j a) := rfl

end

attribute [local irreducible] boundedFlatAffineSectionPrespectrumFunctor
  boundedFlatAffineSectionOpenPrespectrumFunctor boundedFlatAffineSectionOpenBassSeed
  boundedFlatAffineSectionBassUnderSeed boundedFlatAffineSectionOpenPrespectrumTransformation

/-- The strict fine-to-coarse natural arrow preserves the exact original seed transformations. -/
theorem boundedFlatAffineSectionOpenBassSeed_changeWeak :
    boundedFlatAffineSectionBassUnderSeed R ≫
        (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedFlatAffineSectionOpenPrespectrumTransformation j) =
      boundedFlatAffineSectionOpenPrespectrumTransformation j ≫
        boundedFlatAffineSectionOpenBassSeed j := by
  apply NatTrans.ext
  funext a
  simpa only [NatTrans.comp_app, boundedFlatAffineSectionOpenBassSeed_app,
    boundedFlatAffineSectionOpenBassChangeWeak_functor_app,
    boundedFlatAffineSectionBassUnderSeed_app] using
      boundedFlatAffineSectionOpenBassSeedMap_changeWeak j a

end Quillen.PerfectComplexes
