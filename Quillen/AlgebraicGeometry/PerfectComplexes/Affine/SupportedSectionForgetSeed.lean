/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionForgetLaurent
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionBassSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassSeed
public import Quillen.KTheory.Bass.StrictUnderDiagram

/-!
# Original supported and ambient Bass seeds commute with support inclusion

The original support-forgetting natural arrow gives the actual four-corner Laurent square,
cone map and unchanged null cylinder. Together with the whole original scalar forget track,
these prove compatibility of the two constructed Bass seeds. No seed square is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The actual four support inclusions form the unchanged strict Laurent square map. -/
def boundedFlatAffineSupportedSectionBassSquareForget (a : Under R) :
    boundedFlatAffineSupportedSectionBassSquare j a ⟶ boundedFlatAffineSectionBassSquare a.right :=
  ((Functor.mapArrowFunctor (Arrow (Under R)) (Arrow LoopPrespectrum.{u+1})).map
    ((Functor.mapArrowFunctor (Under R) LoopPrespectrum.{u+1}).map
      (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j))).app
        (laurentUnderSquare R a)

/-- The existing original mapping-cone functor gives the actual support-forgetting cone map. -/
def boundedFlatAffineSupportedSectionBassConeForget (a : Under R) :
    boundedFlatAffineSupportedSectionBassCone j a ⟶ boundedFlatAffineSectionBassCone a.right :=
  mappingConeMap (strictSquareComparisonFunctor.map
    (boundedFlatAffineSupportedSectionBassSquareForget j a))

/-- The complete original null cylinder is preserved at the identical time. -/
theorem boundedFlatAffineSupportedSectionBassNullHomotopy_forget_apply
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineSupportedSectionBassConeForget j a).map n
        ((boundedFlatAffineSupportedSectionBassNullHomotopy j a).level n (t, x)) =
      (boundedFlatAffineSectionBassNullHomotopy a.right).level n
        (t, (boundedFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a)).map n x) :=
  StrictSquare.sourceNullHomotopy_naturality_apply
    (boundedFlatAffineSupportedSectionBassSquareForget j a) n t x

/-- The two genuinely constructed original seeds commute with actual support inclusion. -/
theorem boundedFlatAffineSupportedSectionBassSeedMap_forget (a : Under R) :
    boundedFlatAffineSupportedSectionBassSeedMap j a ≫
        parameterLoopingMap (boundedFlatAffineSupportedSectionBassConeForget j a) =
      (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j).app a ≫
        boundedFlatAffineSectionBassSeedMap a.right := by
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    change (mappingConeInclusion
      (StrictSquare.comparison (boundedFlatAffineSectionBassSquare a.right))).map n
        ((boundedFlatAffineSupportedSectionForgetPrespectrumMap
          (inclusion j ((laurentUnderFunctor R).obj a))).map n
          ((boundedFlatAffineSupportedDiagramLaurentHomotopy j a).level n (t, x))) =
      (mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineSectionBassSquare a.right))).map n
          ((boundedFlatAffineSectionLaurentUnitHomotopy a.right).level n
            (t, (boundedFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a)).map n x))
    rw [boundedFlatAffineSupportedDiagramLaurentHomotopy_forget_apply]
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact boundedFlatAffineSupportedSectionBassNullHomotopy_forget_apply j a n t x

/-- The target seed is exactly the constructed ambient seed restricted along Under.forget. -/
def boundedFlatAffineSectionBassUnderSeed (R : CommRingCat.{u}) :
    Under.forget R ⋙ boundedFlatAffineSectionPrespectrumFunctor ⟶
      (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).obj
        (Under.forget R ⋙ boundedFlatAffineSectionPrespectrumFunctor) :=
  KTheory.Bass.strictRingDiagramUnderSeed R boundedFlatAffineSectionBassSeed

section
attribute [local irreducible] boundedFlatAffineSectionPrespectrumFunctor
  boundedFlatAffineSupportedSectionPrespectrumFunctor
  boundedFlatAffineSupportedSectionForgetPrespectrumTransformation

/-- The existing Bass functor acts by the same actual looped support cone map. -/
theorem boundedFlatAffineSupportedSectionBassForget_functor_app (a : Under R) :
    ((KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j)).app a =
      parameterLoopingMap (boundedFlatAffineSupportedSectionBassConeForget j a) := rfl

/-- Restriction retains the unchanged ambient constructed seed at the actual algebra. -/
theorem boundedFlatAffineSectionBassUnderSeed_app (a : Under R) :
    (boundedFlatAffineSectionBassUnderSeed R).app a =
      boundedFlatAffineSectionBassSeedMap a.right :=
  (KTheory.Bass.strictRingDiagramUnderSeed_app R boundedFlatAffineSectionBassSeed a).trans
    (boundedFlatAffineSectionBassSeed_app a.right)

end

attribute [local irreducible] boundedFlatAffineSectionPrespectrumFunctor
  boundedFlatAffineSupportedSectionPrespectrumFunctor
attribute [local irreducible] boundedFlatAffineSupportedSectionBassSeed
  boundedFlatAffineSectionBassSeed boundedFlatAffineSectionBassUnderSeed
  boundedFlatAffineSupportedSectionForgetPrespectrumTransformation

/-- The whole strict natural arrow respects the same two original seed transformations. -/
theorem boundedFlatAffineSupportedSectionBassSeed_forget :
    boundedFlatAffineSupportedSectionBassSeed j ≫
        (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j) =
      boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j ≫
        boundedFlatAffineSectionBassUnderSeed R := by
  apply NatTrans.ext
  funext a
  simpa only [NatTrans.comp_app, boundedFlatAffineSupportedSectionBassSeed_app,
    boundedFlatAffineSupportedSectionBassForget_functor_app,
    boundedFlatAffineSectionBassUnderSeed_app] using
      boundedFlatAffineSupportedSectionBassSeedMap_forget j a

end Quillen.PerfectComplexes
