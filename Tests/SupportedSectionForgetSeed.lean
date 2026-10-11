/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SupportedSectionForgetSeed

/-!
# Original support-forgetting Bass-seed consumers

The source corner, Laurent cone face, whole null track, loop coordinate and independent
structure time are retained. The target seed is the original constructed ambient seed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PolynomialBaseChange
open Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.Tests.SupportedSectionForgetSeed
open PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The actual source corner is the unchanged original supported section inclusion. -/
theorem original_source_corner (a : Under R) :
    (boundedFlatAffineSupportedSectionBassSquareForget j a).left.left =
      boundedFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a) := rfl

/-- The Laurent face uses the same original support map and the same cone inclusion. -/
theorem original_laurent_cone_face (a : Under R) (n : ℕ)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj
      ((laurentUnderFunctor R).obj a)).space n) :
    (boundedFlatAffineSupportedSectionBassConeForget j a).map n
        ((mappingConeInclusion
          (StrictSquare.comparison (boundedFlatAffineSupportedSectionBassSquare j a))).map n x) =
      (mappingConeInclusion
        (StrictSquare.comparison (boundedFlatAffineSectionBassSquare a.right))).map n
          ((boundedFlatAffineSupportedSectionForgetPrespectrumMap
            (inclusion j ((laurentUnderFunctor R).obj a))).map n x) := rfl

/-- The whole original source-null cylinder keeps its exact time under inclusion. -/
theorem original_null_track (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineSupportedSectionBassConeForget j a).map n
        ((boundedFlatAffineSupportedSectionBassNullHomotopy j a).level n (t, x)) =
      (boundedFlatAffineSectionBassNullHomotopy a.right).level n
        (t, (boundedFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a)).map n x) :=
  boundedFlatAffineSupportedSectionBassNullHomotopy_forget_apply j a n t x

/-- Every original seed loop value commutes with the actual looped cone inclusion. -/
theorem original_seed_loop_value (a : Under R) (n : ℕ) (t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    Path.toContinuousMap
        ((parameterLoopingMap (boundedFlatAffineSupportedSectionBassConeForget j a)).map n
          ((boundedFlatAffineSupportedSectionBassSeedMap j a).map n x)) t =
      Path.toContinuousMap ((boundedFlatAffineSectionBassSeedMap a.right).map n
        (((boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j).app a).map n x))
          t :=
  congrArg (fun g ↦ Path.toContinuousMap (g.map n x) t)
    (boundedFlatAffineSupportedSectionBassSeedMap_forget j a)

/-- Structure time and original null-cylinder time stay independent after support inclusion. -/
theorem original_independent_times (a : Under R) (n : ℕ) (s t : unitInterval)
    (x : ((boundedFlatAffineSupportedSectionPrespectrumFunctor j).obj a).space n) :
    (boundedFlatAffineSectionBassCone a.right).structureMap n
        ((boundedFlatAffineSupportedSectionBassConeForget j a).map n
          ((boundedFlatAffineSupportedSectionBassNullHomotopy j a).level n (t, x))) s =
      (boundedFlatAffineSectionBassCone a.right).structureMap n
        ((boundedFlatAffineSectionBassNullHomotopy a.right).level n
          (t, (boundedFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a)).map n x)) s :=
  congrArg (fun y ↦ (boundedFlatAffineSectionBassCone a.right).structureMap n y s)
    (boundedFlatAffineSupportedSectionBassNullHomotopy_forget_apply j a n t x)

attribute [local irreducible] boundedFlatAffineSectionPrespectrumFunctor
  boundedFlatAffineSupportedSectionPrespectrumFunctor

/-- Restriction uses the unchanged ambient constructed Laurent seed at the original ring. -/
theorem original_ambient_seed (a : Under R) :
    (boundedFlatAffineSectionBassUnderSeed R).app a =
      boundedFlatAffineSectionBassSeedMap a.right :=
  boundedFlatAffineSectionBassUnderSeed_app a

/-- The actual Bass endofunctor image gives the original strict natural seed square. -/
theorem original_natural_seed_square :
    boundedFlatAffineSupportedSectionBassSeed j ≫
        (KTheory.Bass.strictDiagramFunctor (laurentUnderSquareFunctor R)).map
          (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j) =
      boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j ≫
        boundedFlatAffineSectionBassUnderSeed R :=
  boundedFlatAffineSupportedSectionBassSeed_forget j

end Quillen.Tests.SupportedSectionForgetSeed
