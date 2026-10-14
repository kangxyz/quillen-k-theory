/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeBinaryComparison
public import Quillen.Topology.Prespectrum.RelativeOperationEvaluation
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SplitTripleParameters
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexTriangleWhiskering
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexTriangleSourceTransport
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TripleTrack

/-! Whole native correspondence for the actual six split-triple surfaces. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.SplitTripleSimplex
variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- The first whole native binary face uses its exact old two parameters. -/
theorem leftFirst_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n (leftFirstParameter (r, s), x) =
      (boundedFlatNormalizedCompTrackComparison f (g ≫ h)).level n (r, (s, x)) := by
  exact (leftFirstParameter_lift f g h n r s x).trans
    (BinaryNormalizationSimplex.native_apply f (g ≫ h) n r s x).symm

/-- The second whole left face retains literal native postcomposition. -/
theorem leftSecond_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n (leftSecondParameter (r, s), x) =
      ((boundedFlatNormalizedCompTrackComparison g h).postcomp
        (boundedFlatPerfectPrespectrumMap f)).level n (r, (s, x)) := by
  refine (leftSecondParameter_lift f g h n r s x).trans ?_
  trans ((prespectrumTransformationCompositionHomotopy
    (BinaryNormalizationSimplex.first g h).hom (BinaryNormalizationSimplex.second g h).hom
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen Y)).waldhausen.weq_iso _ inferInstance)
    (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen Y)).waldhausen.weq_iso _
      inferInstance)).postcomp
    (boundedFlatPerfectPrespectrumMap f)).level n (r, (s, x))
  · exact transformationComposition_postcomp
      (F := BinaryNormalizationSimplex.sourceMap g h)
      (G := BinaryNormalizationSimplex.intermediateMap g h)
      (H := BinaryNormalizationSimplex.targetMap g h)
      (BinaryNormalizationSimplex.first g h).hom (BinaryNormalizationSimplex.second g h).hom
      (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen Y)).waldhausen.weq_iso _ inferInstance)
      (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen Y)).waldhausen.weq_iso _ inferInstance)
      (modelMap _ _ (boundedFlatNormalizedPullback_exact f)
        (boundedFlatNormalizedPullback_obj_zero f)) n r s x
  · exact congrArg ((boundedFlatPerfectPrespectrumMap f).map n)
      (BinaryNormalizationSimplex.native_apply g h n r s x).symm

/-- The second whole right face retains literal native precomposition. -/
theorem rightSecond_native (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen T)).space n) :
    prespectrumSimplexFamily (simplex f g h) n (rightSecondParameter (r, s), x) =
      (Homotopy.RelHomotopy.precomp (boundedFlatPerfectPrespectrumMap h)
        (boundedFlatNormalizedCompTrackComparison f g)).level n (r, (s, x)) := by
  refine (rightSecondParameter_lift f g h n r s x).trans ?_
  trans (Homotopy.RelHomotopy.precomp (boundedFlatPerfectPrespectrumMap h)
    (prespectrumTransformationCompositionHomotopy
      (BinaryNormalizationSimplex.first f g).hom (BinaryNormalizationSimplex.second f g).hom
      (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
      (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
        inferInstance))).level n (r, (s, x))
  · exact transformationComposition_precomp
      (F := BinaryNormalizationSimplex.sourceMap f g)
      (G := BinaryNormalizationSimplex.intermediateMap f g)
      (H := BinaryNormalizationSimplex.targetMap f g)
      (BinaryNormalizationSimplex.first f g).hom (BinaryNormalizationSimplex.second f g).hom
      (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
      (fun _ ↦ (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
      (modelMap _ _ (boundedFlatNormalizedPullback_exact h)
        (boundedFlatNormalizedPullback_obj_zero h)) n r s x
  · exact (Homotopy.RelHomotopy.level_eq_precomp_apply _ _
      (boundedFlatPerfectPrespectrumMap h) n (BinaryNormalizationSimplex.native_level f g n)
      r s x).symm

end Quillen.PerfectComplexes.SplitTripleSimplex
