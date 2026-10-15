/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionGradingNullSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionBassSeed
public import Quillen.KTheory.Bass.StrictDiagramHomotopy

/-!
# The canonical grading null preserves the original Bass seeds

Every time slice of the original coefficient-natural null gives its actual four-corner
Laurent square. The scalar-action and localization-null times are independent in the
interchange identity. The seed retains its prescribed concatenated track; localization-null
time and the resulting output-loop coordinate remain independent in the seed equation.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- Each time of the same canonical localization null is a strict coefficient-natural map. -/
def boundedFlatAffineFullOpenSectionGradingNullTimeSlice (s : unitInterval) :
    boundedFlatAffineSectionOpenPrespectrumFunctor j ⟶
      boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j :=
  diagramHomotopyAt
    (η := boundedFlatAffineSectionFullOpenPrespectrumTransformation j ≫
      boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j)
    (θ := diagramZeroMap (boundedFlatAffineSectionOpenPrespectrumFunctor j)
      (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j))
    (boundedFlatAffineFullOpenSectionGradingDiagramNull j).homotopy
    (boundedFlatAffineFullOpenSectionGradingDiagramNull j).naturality s

private def gradingSeedSquareMap
    (η : boundedFlatAffineSectionOpenPrespectrumFunctor j ⟶
      boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j) (a : Under R) :
    boundedFlatAffineSectionOpenBassSquare j a ⟶
      boundedFlatAffineFullOpenGradedSectionBassSquare j a :=
  diagramSquareMap η (laurentUnderSquare R a)

private def gradingSeedConeMap
    (η : boundedFlatAffineSectionOpenPrespectrumFunctor j ⟶
      boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j) (a : Under R) :
    boundedFlatAffineSectionOpenBassCone j a ⟶
      boundedFlatAffineFullOpenGradedSectionBassCone j a :=
  mappingConeMap (strictSquareComparisonFunctor.map (gradingSeedSquareMap j η a))

private theorem gradingSeedCylinder_apply
    (η : boundedFlatAffineSectionOpenPrespectrumFunctor j ⟶
      boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j)
    (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a).space n) :
    (gradingSeedConeMap j η a).map n
        ((boundedFlatAffineSectionOpenBassNullHomotopy j a).level n (t, x)) =
      (boundedFlatAffineFullOpenGradedSectionBassNullHomotopy j a).level n
        (t, (η.app a).map n x) :=
  StrictSquare.sourceNullHomotopy_naturality_apply (gradingSeedSquareMap j η a) n t x

private def GradingSeedLaurentCompatible
    (η : boundedFlatAffineSectionOpenPrespectrumFunctor j ⟶
      boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j) : Prop :=
  ∀ (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a).space n),
    (η.app ((laurentUnderFunctor R).obj a)).map n
        ((boundedFlatAffineSectionOpenDiagramLaurentHomotopy j a).level n (t, x)) =
      (boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a).level n
        (t, (η.app a).map n x)

private theorem gradingSeedMap_square
    (η : boundedFlatAffineSectionOpenPrespectrumFunctor j ⟶
      boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j)
    (hη : GradingSeedLaurentCompatible j η) (a : Under R) :
    boundedFlatAffineSectionOpenBassSeedMap j a ≫
        parameterLoopingMap (gradingSeedConeMap j η a) =
      η.app a ≫ boundedFlatAffineFullOpenGradedSectionBassSeedMap j a := by
  apply Homotopy.nullLoopMap_naturality
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    change (mappingConeInclusion
      (StrictSquare.comparison (boundedFlatAffineFullOpenGradedSectionBassSquare j a))).map n
        ((η.app ((laurentUnderFunctor R).obj a)).map n
          ((boundedFlatAffineSectionOpenDiagramLaurentHomotopy j a).level n (t, x))) =
      (mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineFullOpenGradedSectionBassSquare j a))).map n
          ((boundedFlatAffineFullOpenGradedSectionDiagramLaurentHomotopy j a).level n
            (t, (η.app a).map n x))
    rw [hη]
  · intro n
    apply ContinuousMap.ext
    rintro ⟨t, x⟩
    exact gradingSeedCylinder_apply j η a n t x

section
attribute [local irreducible] boundedFlatAffineSectionOpenPrespectrumFunctor
  boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor

private theorem gradingSeedFunctor_app
    (η : boundedFlatAffineSectionOpenPrespectrumFunctor j ⟶
      boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j) (a : Under R) :
    ((strictDiagramFunctor (laurentUnderSquareFunctor R)).map η).app a =
      parameterLoopingMap (gradingSeedConeMap j η a) := rfl

end

section
attribute [local irreducible] boundedFlatAffineSectionOpenPrespectrumFunctor
  boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor
  boundedFlatAffineSectionOpenBassSeed boundedFlatAffineFullOpenGradedSectionBassSeed

private theorem gradingSeed_square
    (η : boundedFlatAffineSectionOpenPrespectrumFunctor j ⟶
      boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j)
    (hη : GradingSeedLaurentCompatible j η) :
    boundedFlatAffineSectionOpenBassSeed j ≫
        (strictDiagramFunctor (laurentUnderSquareFunctor R)).map η =
      η ≫ boundedFlatAffineFullOpenGradedSectionBassSeed j := by
  apply NatTrans.ext
  funext a
  simp only [NatTrans.comp_app, boundedFlatAffineSectionOpenBassSeed_app,
    boundedFlatAffineFullOpenGradedSectionBassSeed_app, gradingSeedFunctor_app]
  exact gradingSeedMap_square j η hη a

end

private theorem gradingNullTimeSlice_laurent (s : unitInterval) :
    GradingSeedLaurentCompatible j (boundedFlatAffineFullOpenSectionGradingNullTimeSlice j s) :=
  fun a n t x => boundedFlatAffineFullOpenSectionGradingNullHomotopy_laurent_apply j a n s t x

/-- The same canonical null satisfies the original strict Bass seed square at every time. -/
theorem boundedFlatAffineFullOpenSectionGradingNullTimeSlice_seed (s : unitInterval) :
    boundedFlatAffineSectionOpenBassSeed j ≫
        (strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedFlatAffineFullOpenSectionGradingNullTimeSlice j s) =
      boundedFlatAffineFullOpenSectionGradingNullTimeSlice j s ≫
        boundedFlatAffineFullOpenGradedSectionBassSeed j :=
  gradingSeed_square j (boundedFlatAffineFullOpenSectionGradingNullTimeSlice j s)
    (gradingNullTimeSlice_laurent j s)

/-- The original Bass image of the canonical null keeps the same natural time slice. -/
theorem boundedFlatAffineFullOpenSectionGradingBassNullHomotopy_at
    (a : Under R) (s : unitInterval) :
    (strictDiagramNullHomotopy
      (boundedFlatAffineSectionFullOpenPrespectrumTransformation j)
      (boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j)
      (boundedFlatAffineFullOpenSectionGradingDiagramNull j).homotopy
      (boundedFlatAffineFullOpenSectionGradingDiagramNull j).naturality
      (laurentUnderSquareFunctor R) a).at s =
      ((strictDiagramFunctor (laurentUnderSquareFunctor R)).map
        (boundedFlatAffineFullOpenSectionGradingNullTimeSlice j s)).app a :=
  strictDiagramMapHomotopy_at
    (η := boundedFlatAffineSectionFullOpenPrespectrumTransformation j ≫
      boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j)
    (θ := diagramZeroMap (boundedFlatAffineSectionOpenPrespectrumFunctor j)
      (boundedFlatAffineFullOpenGradedSectionPrespectrumFunctor j))
    (boundedFlatAffineFullOpenSectionGradingDiagramNull j).homotopy
    (boundedFlatAffineFullOpenSectionGradingDiagramNull j).naturality
    (laurentUnderSquareFunctor R) a s

/-- The original Bass null commutes with the unchanged seeds as whole based-loop values. -/
theorem boundedFlatAffineFullOpenSectionGradingBassNullHomotopy_seed
    (a : Under R) (n : ℕ) (s : unitInterval)
    (x : ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a).space n) :
    (strictDiagramNullHomotopy
      (boundedFlatAffineSectionFullOpenPrespectrumTransformation j)
      (boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j)
      (boundedFlatAffineFullOpenSectionGradingDiagramNull j).homotopy
      (boundedFlatAffineFullOpenSectionGradingDiagramNull j).naturality
      (laurentUnderSquareFunctor R) a).level n
        (s, (boundedFlatAffineSectionOpenBassSeedMap j a).map n x) =
      (boundedFlatAffineFullOpenGradedSectionBassSeedMap j a).map n
        ((boundedFlatAffineFullOpenSectionGradingNullHomotopy j a).level n (s, x)) := by
  have hs := congrArg (fun f => f.map n
    ((boundedFlatAffineSectionOpenBassSeedMap j a).map n x))
    (boundedFlatAffineFullOpenSectionGradingBassNullHomotopy_at j a s)
  exact hs.trans (congrArg (fun f => (f.app a).map n x)
    (boundedFlatAffineFullOpenSectionGradingNullTimeSlice_seed j s))

/-- Localization-null time and output-loop coordinate remain independent in the seed square. -/
theorem boundedFlatAffineFullOpenSectionGradingBassNullHomotopy_seed_apply
    (a : Under R) (n : ℕ) (s t : unitInterval)
    (x : ((boundedFlatAffineSectionOpenPrespectrumFunctor j).obj a).space n) :
    Path.toContinuousMap
      ((strictDiagramNullHomotopy
        (boundedFlatAffineSectionFullOpenPrespectrumTransformation j)
        (boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j)
        (boundedFlatAffineFullOpenSectionGradingDiagramNull j).homotopy
        (boundedFlatAffineFullOpenSectionGradingDiagramNull j).naturality
        (laurentUnderSquareFunctor R) a).level n
          (s, (boundedFlatAffineSectionOpenBassSeedMap j a).map n x)) t =
      Path.toContinuousMap
        ((boundedFlatAffineFullOpenGradedSectionBassSeedMap j a).map n
          ((boundedFlatAffineFullOpenSectionGradingNullHomotopy j a).level n (s, x))) t :=
  congrArg (fun p => Path.toContinuousMap p t)
    (boundedFlatAffineFullOpenSectionGradingBassNullHomotopy_seed j a n s x)

end Quillen.PerfectComplexes
