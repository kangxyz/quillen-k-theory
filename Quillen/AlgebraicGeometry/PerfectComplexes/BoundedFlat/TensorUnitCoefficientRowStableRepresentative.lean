/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientRowBassComparison
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientKOne
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRowStable
public import Quillen.Topology.Prespectrum.StableLocalization

/-!
# The normalized first-coefficient Bass composite in the stable localization

The numerator is the independently realized first-S tensor cell with the original
inverse-prefix normalization and forward rank-one unit. It is followed by the unchanged
Bass cofiber inclusion. The denominator is the proved stable parameter-looped row comparison,
with its genuine row interchange and degree-zero extension. The whole spectrum normalization
homotopy identifies this explicit roof with the original tensor seed and the forward scalar
seed. The coefficient is anchored to the original perfect unit class by
`tensorUnitCoefficientKOneClass_inclusion`; the operation comparison is the whole homotopy,
not a consequence of that class equality or agreement on stable homotopy groups.

This certifies the restricted normalized coefficient composite at the ambient raw initial
stage. It does not assert descent to every Bass stage or an independent supported target.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- The precise stable denominator preserves the original cone and actual row structure. -/
def boundedFlatCoefficientNormalizedCellRefinement :
    boundedFlatCoefficientBassStep P a ⟶
      parameterLooping (CoefficientBassRowRefinement.carrier P a) :=
  parameterLoopingMap (CoefficientBassRowRefinement.comparison P a)

/-- This actual denominator is stable in every signed degree, with no remaining range premise. -/
theorem boundedFlatCoefficientNormalizedCellRefinement_isStableEquivalence :
    IsStableEquivalence (boundedFlatCoefficientNormalizedCellRefinement P a) :=
  CoefficientBassRowRefinement.parameterComparison_isStableEquivalence P a

/-- The explicit normalized first-coefficient/cofiber roof is a genuine localized morphism. -/
def boundedFlatCoefficientNormalizedCellLocalizedArrow :
    toStableLocalization.obj
        (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))) ⟶
      toStableLocalization.obj (boundedFlatCoefficientBassStep P a) :=
  toStableLocalization.map (boundedFlatCoefficientNormalizedCellBass P a) ≫
    (stableLocalizationIso (boundedFlatCoefficientNormalizedCellRefinement P a)
      (boundedFlatCoefficientNormalizedCellRefinement_isStableEquivalence P a)).inv

/-- Whole parameterized normalization certifies the tensor seed as the actual roof representative.
-/
theorem boundedFlatCoefficientNormalizedCellLocalizedArrow_tensor :
    boundedFlatCoefficientNormalizedCellLocalizedArrow P a =
      toStableLocalization.map (boundedFlatCoefficientTensorBassTransition P a) := by
  unfold boundedFlatCoefficientNormalizedCellLocalizedArrow
  rw [toStableLocalization_map_eq_of_homotopy
    (boundedFlatCoefficientNormalizedCellBassHomotopy P a)]
  change toStableLocalization.map (boundedFlatCoefficientTensorBassTransition P a ≫
    boundedFlatCoefficientNormalizedCellRefinement P a) ≫ _ = _
  rw [CategoryTheory.Functor.map_comp]
  change (toStableLocalization.map (boundedFlatCoefficientTensorBassTransition P a) ≫
      (stableLocalizationIso (boundedFlatCoefficientNormalizedCellRefinement P a)
        (boundedFlatCoefficientNormalizedCellRefinement_isStableEquivalence P a)).hom) ≫ _ = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The original forward scalar seed represents the normalized first-S coefficient composite. -/
theorem boundedFlatCoefficientNormalizedCellLocalizedArrow_seed :
    boundedFlatCoefficientNormalizedCellLocalizedArrow P a =
      toStableLocalization.map (boundedFlatCoefficientBassTransition P a) :=
  (boundedFlatCoefficientNormalizedCellLocalizedArrow_tensor P a).trans
    (toStableLocalization_map_eq_of_homotopy
      (boundedFlatCoefficientTensorBassTransitionHomotopy P a))

/-- Before cancellation, the complete diagram agrees through the specified actual stable leg. -/
theorem boundedFlatCoefficientNormalizedCellLocalizedArrow_refinement :
    boundedFlatCoefficientNormalizedCellLocalizedArrow P a ≫
      toStableLocalization.map (boundedFlatCoefficientNormalizedCellRefinement P a) =
        toStableLocalization.map (boundedFlatCoefficientNormalizedCellBass P a) := by
  unfold boundedFlatCoefficientNormalizedCellLocalizedArrow
  change (_ ≫ (stableLocalizationIso (boundedFlatCoefficientNormalizedCellRefinement P a)
    (boundedFlatCoefficientNormalizedCellRefinement_isStableEquivalence P a)).inv) ≫
      (stableLocalizationIso (boundedFlatCoefficientNormalizedCellRefinement P a)
        (boundedFlatCoefficientNormalizedCellRefinement_isStableEquivalence P a)).hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Quillen.PerfectComplexes
