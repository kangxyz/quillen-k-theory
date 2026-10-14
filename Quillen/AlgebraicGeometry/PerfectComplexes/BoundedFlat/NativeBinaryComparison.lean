/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BinaryNormalizationSimplex
public import Quillen.Topology.Prespectrum.RelativeLevelEvaluation

/-! Whole native binary comparison in the accepted small-model coordinates. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BinaryNormalizationSimplex
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- Full native binary comparison equals the previously identified original small-model triangle. -/
theorem native_level (n : ℕ) :
    ((boundedFlatNormalizedCompTrackComparison f g).level n).toContinuousMap =
      ((prespectrumTransformationCompositionHomotopy (first f g).hom (second f g).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance)).level n).toContinuousMap :=
  boundedFlatNormalizedCompTrackComparison_whole_level f g n
/-- Pointwise evaluation of the same whole native comparison, at all original parameters. -/
theorem native_apply (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen Z)).space n) :
    (boundedFlatNormalizedCompTrackComparison f g).level n (r, (s, x)) =
      (prespectrumTransformationCompositionHomotopy (first f g).hom (second f g).hom
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance)).level n (r, (s, x)) :=
  Homotopy.RelHomotopy.level_eq_apply _ _ n (native_level f g n) r s x

end Quillen.PerfectComplexes.BinaryNormalizationSimplex
