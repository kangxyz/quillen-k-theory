/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedCoefficientSmallModel
public import Quillen.Waldhausen.SConstruction.Iterated.RowTransformationSpectrum

/-!
# The genuine supported tensor coefficient cell in its row spectrum

All objects and structure maps use the original supported Waldhausen category. The independently
constructed first tensor row agrees, as a whole double cylinder, with the finite transformation
row construction. Its realization retains the separate row, unit-edge and zero-level loop times.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes
variable {S T : Scheme.OpenPairs.{u}} (p : S ⟶ T) (r : (Γ(S.obj.right, ⊤))ˣ)

/-- The original exact supported tensor-pullback prespectrum map. -/
def tensorSupportedPairPrespectrumMap :=
  exactOriginalPrespectrumMap (boundedFlatPerfectSupportedWaldhausen T.obj.hom)
    (boundedFlatPerfectSupportedWaldhausen S.obj.hom) (tensorSupportedPair_exact p)

/-- The original forward tensor coefficient acts within the supported target. -/
def tensorSupportedPairHomotopy :
    Homotopy (tensorSupportedPairPrespectrumMap p) (tensorSupportedPairPrespectrumMap p) :=
  exactOriginalPrespectrumIsoHomotopy (boundedFlatPerfectSupportedWaldhausen T.obj.hom)
    (boundedFlatPerfectSupportedWaldhausen S.obj.hom)
    (tensorSupportedPair_exact p) (tensorSupportedPair_exact p)
    (tensorSupportedPairAutomorphism p r)

/-- Its small-model formula retains the original selected-zero normalization. -/
theorem tensorSupportedPairHomotopy_model :
    tensorSupportedPairHomotopy p r =
      prespectrumTransformationHomotopy (tensorSupportedPairModelTransformation p r)
        (tensorSupportedPairModelTransformation_weak p r) := rfl

/-- Finite S-prolongation of the actual supported row transformation. -/
def tensorSupportedPairCoefficientStageCylinder (k : ℕ) :=
  rowTransformationCylinder (tensorSupportedPairModelTransformation p r)
    (tensorSupportedPairModelTransformation_weak p r) k

/-- At the first row this is the independently constructed genuine tensor coefficient cell. -/
theorem tensorSupportedPairCoefficientStageCylinder_zero :
    tensorSupportedPairCoefficientStageCylinder p r 0 =
      tensorSupportedPairSmallCoefficientCylinder p r :=
  (tensorSupportedPairSmallCoefficientCylinder_row p r).symm

/-- Whole realization with the original two cylinder isomorphisms, row time outermost. -/
def tensorSupportedPairCoefficientStageRealization (k : ℕ) :=
  rowTransformationRealization (tensorSupportedPairModelTransformation p r)
    (tensorSupportedPairModelTransformation_weak p r) k

/-- The complete supported row-spectrum homotopy. -/
def tensorSupportedPairCoefficientSpectrumHomotopy :
    Homotopy
      (tensorSupportedPairPrespectrumMap p ≫
        rowStabilizationMap (modelOf (boundedFlatPerfectSupportedWaldhausen S.obj.hom)))
      (tensorSupportedPairPrespectrumMap p ≫
        rowStabilizationMap (modelOf (boundedFlatPerfectSupportedWaldhausen S.obj.hom))) :=
  (tensorSupportedPairHomotopy p r).postcomp
    (rowStabilizationMap (modelOf (boundedFlatPerfectSupportedWaldhausen S.obj.hom)))

/-- Every positive level is exactly the realized supported double cylinder. -/
theorem tensorSupportedPairCoefficientSpectrumHomotopy_succ
    (k : ℕ) (t s : unitInterval)
    (x : stageSpace k (modelOf (boundedFlatPerfectSupportedWaldhausen T.obj.hom))) :
    Path.toContinuousMap
      ((tensorSupportedPairCoefficientSpectrumHomotopy p r).level (k + 1) (t, x)) s =
      tensorSupportedPairCoefficientStageRealization p r k (s, (t, x)) :=
  rowTransformationSpectrumHomotopy_succ (tensorSupportedPairModelTransformation p r)
    (tensorSupportedPairModelTransformation_weak p r) k t s x

/-- The original zero extension keeps input-loop time independent from both coefficient times. -/
theorem tensorSupportedPairCoefficientSpectrumHomotopy_zero (t a s : unitInterval)
    (γ : Path (stagePoint 0 (modelOf (boundedFlatPerfectSupportedWaldhausen T.obj.hom)))
      (stagePoint 0 (modelOf (boundedFlatPerfectSupportedWaldhausen T.obj.hom)))) :
    Path.toContinuousMap (Path.toContinuousMap
      ((tensorSupportedPairCoefficientSpectrumHomotopy p r).level 0 (t, γ)) a) s =
      tensorSupportedPairCoefficientStageRealization p r 0 (s, (t, γ a)) :=
  rowTransformationSpectrumHomotopy_zero (tensorSupportedPairModelTransformation p r)
    (tensorSupportedPairModelTransformation_weak p r) t a s γ

end Quillen.PerfectComplexes
