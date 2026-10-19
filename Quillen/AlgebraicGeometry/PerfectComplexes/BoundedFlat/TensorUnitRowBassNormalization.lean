/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRowRefinement
public import Quillen.Topology.Prespectrum.RowNormalization
public import Quillen.Topology.Prespectrum.NullLoopNaturality
public import Quillen.Topology.Prespectrum.FiberHomotopySquare

/-!
# Normalization after the actual raw Bass cofiber and its row refinement

The genuine tensor track and the original tensor-unitor/positive-source null are sent through
the unchanged raw Bass cofiber and its actual row comparison. Original inverse-prefix
normalization then has a whole prespectrum homotopy to the original tensor Bass seed followed
by that same comparison. The statement retains every level, including degree zero. Identifying
its source with the independently realized coefficient operation is a separate strict square.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open CommRingCat.PolynomialLaurent
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The original tensor-pullback endpoint followed by the same cofiber and actual row comparison.
-/
def boundedFlatCoefficientTensorRowEndpoint :=
  (boundedFlatPerfectTensorUnitPrespectrumMap (laurentProjection P a) ≫
    mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)) ≫
      CoefficientBassRowRefinement.comparison P a

/-- The genuine tensor track followed by the unchanged actual row comparison. -/
def boundedFlatCoefficientTensorRowTrack :
    Homotopy (boundedFlatCoefficientTensorRowEndpoint P a)
      (boundedFlatCoefficientTensorRowEndpoint P a) :=
  (boundedFlatCoefficientTensorConeTrack P a).postcomp
    (CoefficientBassRowRefinement.comparison P a)

/-- Transport the prescribed tensor-unitor/positive null through exactly the same comparison. -/
def boundedFlatCoefficientTensorRowNull :
    Homotopy (boundedFlatCoefficientTensorRowEndpoint P a)
      (zeroHom _ (CoefficientBassRowRefinement.carrier P a)) :=
  ((boundedFlatCoefficientTensorConeNull P a).postcomp
    (CoefficientBassRowRefinement.comparison P a)).cast rfl (zeroHom_comp _)

/-- The original inverse-prefix operation on the actual cofiber-refined tensor cell. -/
def boundedFlatCoefficientTensorRowNormalizedBass :
    originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a))) ⟶
      parameterLooping (CoefficientBassRowRefinement.carrier P a) :=
  RowRefinement.normalizedOperation (CoefficientBassRowCone.rowSwap P a)
    (CoefficientBassRowCone.rowSwap_point P a) (boundedFlatCoefficientTensorRowEndpoint P a)
    (boundedFlatCoefficientTensorRowTrack P a)

/-- The whole prescribed null word commutes strictly with the actual row comparison. -/
theorem boundedFlatCoefficientTensorRowNullLoop :
    boundedFlatCoefficientTensorBassTransition P a ≫
      parameterLoopingMap (CoefficientBassRowRefinement.comparison P a) =
    (boundedFlatCoefficientTensorRowTrack P a).nullLoopMap
      (boundedFlatCoefficientTensorRowNull P a) := by
  have h := Homotopy.nullLoopMap_naturality (𝟙 _) (CoefficientBassRowRefinement.comparison P a)
    (boundedFlatCoefficientTensorConeTrack P a) (boundedFlatCoefficientTensorRowTrack P a)
    (boundedFlatCoefficientTensorConeNull P a) (boundedFlatCoefficientTensorRowNull P a)
    (fun _ => rfl) (fun _ => rfl)
  simpa only [Category.id_comp, boundedFlatCoefficientTensorBassTransition] using h

/-- A complete spectrum homotopy identifies normalization with the original tensor/null seed. -/
def boundedFlatCoefficientTensorRowNormalization :
    Homotopy (boundedFlatCoefficientTensorRowNormalizedBass P a)
      (boundedFlatCoefficientTensorBassTransition P a ≫
        parameterLoopingMap (CoefficientBassRowRefinement.comparison P a)) :=
  (RowRefinement.normalizationHomotopy (CoefficientBassRowCone.rowSwap P a)
    (CoefficientBassRowCone.rowSwap_point P a) (boundedFlatCoefficientTensorRowEndpoint P a)
    (boundedFlatCoefficientTensorRowTrack P a) (boundedFlatCoefficientTensorRowNull P a)).cast
      rfl (boundedFlatCoefficientTensorRowNullLoop P a).symm

end Quillen.PerfectComplexes
