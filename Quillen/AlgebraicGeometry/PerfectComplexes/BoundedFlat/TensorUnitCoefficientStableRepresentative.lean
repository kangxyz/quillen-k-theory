/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientBassTransition
public import Quillen.Topology.Prespectrum.StableStabilization
public import Quillen.Topology.Prespectrum.ParameterLoopingStableEquivalence
public import Quillen.Topology.Prespectrum.StableLocalization

/-!
# The actual Bass seed represents the genuine stabilized coefficient cell

The independently realized first coefficient cell supplies an actual stabilized arrow. Its
specified denominator is parameter looping of the original loop-tail stabilization, an actual
stable equivalence. The proved whole-map identity identifies the resulting explicit roof with
the actual tensor seed, and the proved whole tensor-unitor/null comparison identifies it with
the original scalar seed in the constructed stable localization. No equality is inferred from
agreement on stable groups, and no point-set inverse or unstabilized homotopy is manufactured.
Identifying this cell/null roof with the inverse-prefix-normalized K-one product still requires
the separate whole parameterized normalization comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The displayed coefficient-cell denominator is the actual parameter-looped stabilization. -/
def boundedFlatCoefficientCellRefinement :
    boundedFlatCoefficientBassStep P a ⟶
      parameterLooping (looping (tail
        (mappingCone (boundedFlatCoefficientBassSquareComparison P a)))) :=
  parameterLoopingMap
    (stabilizationMap (mappingCone (boundedFlatCoefficientBassSquareComparison P a)))

/-- This precise denominator is stable in every integer degree, without a connectivity premise. -/
theorem boundedFlatCoefficientCellRefinement_isStableEquivalence :
    IsStableEquivalence (boundedFlatCoefficientCellRefinement P a) :=
  parameterLoopingMap_isStableEquivalence _ (stabilizationMap_isStableEquivalence _)

/-- The genuine first coefficient cell has a fully specified roof in the stable localization. -/
def boundedFlatCoefficientCellLocalizedArrow :
    toStableLocalization.obj
        (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))) ⟶
      toStableLocalization.obj (boundedFlatCoefficientBassStep P a) :=
  toStableLocalization.map (boundedFlatCoefficientCellBassTransition P a) ≫
    (stableLocalizationIso (boundedFlatCoefficientCellRefinement P a)
      (boundedFlatCoefficientCellRefinement_isStableEquivalence P a)).inv

/-- Whole-map equality, rather than stable-group detection, certifies the actual tensor seed. -/
theorem boundedFlatCoefficientCellLocalizedArrow_tensor :
    boundedFlatCoefficientCellLocalizedArrow P a =
      toStableLocalization.map (boundedFlatCoefficientTensorBassTransition P a) := by
  unfold boundedFlatCoefficientCellLocalizedArrow
  rw [boundedFlatCoefficientCellBassTransition_eq, CategoryTheory.Functor.map_comp]
  change (toStableLocalization.map (boundedFlatCoefficientTensorBassTransition P a) ≫
      (stableLocalizationIso (boundedFlatCoefficientCellRefinement P a)
        (boundedFlatCoefficientCellRefinement_isStableEquivalence P a)).hom) ≫ _ = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The original forward scalar Bass seed is the proved representative of the genuine cell roof.
-/
theorem boundedFlatCoefficientCellLocalizedArrow_seed :
    boundedFlatCoefficientCellLocalizedArrow P a =
      toStableLocalization.map (boundedFlatCoefficientBassTransition P a) :=
  (boundedFlatCoefficientCellLocalizedArrow_tensor P a).trans
    (toStableLocalization_map_eq_of_homotopy
      (boundedFlatCoefficientTensorBassTransitionHomotopy P a))

end Quillen.PerfectComplexes
