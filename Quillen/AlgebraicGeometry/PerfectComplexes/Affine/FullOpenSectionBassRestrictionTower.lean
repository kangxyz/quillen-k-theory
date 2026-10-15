/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionOpenBassTower
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassTower
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionDiagram
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionBassGradingTower
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionGradingNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionConeStable
public import Quillen.KTheory.Bass.ModelDiagramIterateCofiberPreservation
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenSectionRestrictionSeed
public import Quillen.KTheory.Bass.StrictDiagramMap

/-!
# The original coarse-to-full section restriction through the Bass tower

The strict Bass iterate acts on the original coefficient-natural section restriction.
Its finite components retain the actual coarse relative-open and fine full-open stages.
The original restriction seed square gives the actual finite restriction transition equations.
The same canonical whole null is iterated unchanged, and its original cone descent to the
quotient-graded stage is stable in every signed degree. Whole-null transition coherence is separate.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- Each finite restriction is the literal Bass iterate of the original transformation. -/
def boundedFlatAffineSectionFullOpenBassRestriction (i : ℕ) :
    boundedFlatAffineSectionOpenBassDiagram j i ⟶
      boundedFlatAffineFullOpenSectionBassDiagram j i :=
  (strictDiagramIterate (laurentUnderSquareFunctor R) i).map
    (boundedFlatAffineSectionFullOpenPrespectrumTransformation j)

/-- The initial arrow is exactly the original coarse-to-full section restriction. -/
theorem boundedFlatAffineSectionFullOpenBassRestriction_zero :
    boundedFlatAffineSectionFullOpenBassRestriction j 0 =
      boundedFlatAffineSectionFullOpenPrespectrumTransformation j := rfl

/-- The original seed square preserves every actual coarse and fine restriction transition. -/
theorem boundedFlatAffineSectionFullOpenBassRestriction_transition (i : ℕ) :
    boundedFlatAffineSectionFullOpenBassRestriction j i ≫
        boundedFlatAffineFullOpenSectionBassTransition j i =
      boundedFlatAffineSectionOpenBassTransition j i ≫
        boundedFlatAffineSectionFullOpenBassRestriction j (i + 1) :=
  (strictDiagramTransition_map (laurentUnderSquareFunctor R)
    (boundedFlatAffineSectionOpenBassSeed j) (boundedFlatAffineFullOpenSectionBassSeed j)
    (boundedFlatAffineSectionFullOpenPrespectrumTransformation j)
    (boundedFlatAffineSectionFullOpenBassSeed_restriction j) i).symm

/-- The actual finite Model stages give cone-to-fiber excision for the unchanged restriction. -/
theorem boundedFlatAffineSectionFullOpenBassRestriction_coneFiber_isStableEquivalence
    (i : ℕ) (a : Under R) :
    IsStableEquivalence (mappingConeFiberComparison
      ((boundedFlatAffineSectionFullOpenBassRestriction j i).app a)) :=
  modelDiagramIterateArrow_coneFiber_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedFlatAffineSectionOpenModelFunctor j)
    (boundedFlatAffineFullOpenSectionModelFunctor j)
    (boundedFlatAffineSectionFullOpenPrespectrumTransformation j) i a

variable [CompactSpace U]

/-- Iterate the same prescribed coefficient-natural restriction/grading null unchanged. -/
def boundedFlatAffineSectionFullOpenBassRestrictionGradingNull (i : ℕ) :
    DiagramNullHomotopy (boundedFlatAffineSectionFullOpenBassRestriction j i)
      (boundedFlatAffineFullOpenSectionBassGrading j i) :=
  strictDiagramIterateNull (laurentUnderSquareFunctor R)
    (boundedFlatAffineFullOpenSectionGradingDiagramNull j) i

/-- The original finite restriction cone descends along its same complete iterated null. -/
def boundedFlatAffineSectionFullOpenBassGradingConeMap (i : ℕ) :
    mappingConeDiagram (boundedFlatAffineSectionFullOpenBassRestriction j i) ⟶
      boundedFlatAffineFullOpenGradedSectionBassDiagram j i :=
  mappingConeDescTransformation (boundedFlatAffineSectionFullOpenBassRestriction j i)
    (boundedFlatAffineFullOpenSectionBassGrading j i)
    (boundedFlatAffineSectionFullOpenBassRestrictionGradingNull j i).homotopy
    (boundedFlatAffineSectionFullOpenBassRestrictionGradingNull j i).naturality

/-- The exact target face of the original finite restriction cone is its original grading map. -/
theorem boundedFlatAffineSectionFullOpenBassGradingConeMap_inclusion (i : ℕ) (a : Under R) :
    mappingConeInclusion ((boundedFlatAffineSectionFullOpenBassRestriction j i).app a) ≫
        (boundedFlatAffineSectionFullOpenBassGradingConeMap j i).app a =
      (boundedFlatAffineFullOpenSectionBassGrading j i).app a := mappingConeInclusion_desc _ _ _

/-- The original stable section cone descent stays stable at every actual finite Bass stage. -/
theorem boundedFlatAffineSectionFullOpenBassGradingConeMap_isStableEquivalence
    (i : ℕ) (a : Under R) :
    IsStableEquivalence ((boundedFlatAffineSectionFullOpenBassGradingConeMap j i).app a) :=
  modelDiagramIterateCofiberDesc_isStableEquivalence (laurentUnderSquareFunctor R)
    (boundedFlatAffineSectionOpenModelFunctor j)
    (boundedFlatAffineFullOpenSectionModelFunctor j)
    (boundedFlatAffineFullOpenGradedSectionModelFunctor j)
    (boundedFlatAffineSectionFullOpenPrespectrumTransformation j)
    (boundedFlatAffineFullOpenSectionGradingPrespectrumTransformation j)
    (boundedFlatAffineFullOpenSectionGradingDiagramNull j)
    (fun a ↦ boundedFlatAffineFullOpenSectionConeDesc_isStableEquivalence j a
      (boundedFlatAffineFullOpenSectionGradingNullHomotopy j a)) i a

end Quillen.PerfectComplexes
