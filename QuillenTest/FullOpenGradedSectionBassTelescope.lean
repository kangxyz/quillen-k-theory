/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FullOpenGradedSectionBassTelescope

/-!
# Original-map consumers of graded Bass telescope vanishing

The signed consumer includes negative degrees. The map consumers preserve the actual original
stage-zero seed and stage inclusion, rather than replacing the tower by a zero diagram.
-/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace QuillenTest.FullOpenGradedSectionBassTelescope

open Quillen
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R)
  [IsOpenImmersion j] [CompactSpace U]

/-- The first original transition is exactly the accepted forward Laurent seed. -/
theorem graded_telescope_original_seed :
    boundedFlatAffineFullOpenGradedSectionBassTransition j 0 =
      boundedFlatAffineFullOpenGradedSectionBassSeed j :=
  boundedFlatAffineFullOpenGradedSectionBassTransition_zero j

/-- Every signed stable group of the literal telescope is zero, without a stage-group premise. -/
theorem graded_telescope_signed_class_zero (a : Under R) (d : ℤ)
    (x : stableHomotopyGroup
      ((boundedFlatAffineFullOpenGradedSectionBassTelescopeFunctor j).obj a) d) : x = 0 :=
  boundedFlatAffineFullOpenGradedSectionBassTelescope_stableClass_eq_zero j a d x

/-- An explicitly negative degree uses the unchanged initial stage inclusion. -/
theorem graded_telescope_original_inclusion_negative (a : Under R) (n : ℕ) :
    (stableHomotopyFunctor (-(n : ℤ) - 1)).map
      ((boundedFlatAffineFullOpenGradedSectionBassTelescopeInclusion j 0).app a) = 0 :=
  boundedFlatAffineFullOpenGradedSectionBassTelescopeInclusion_stableMap_eq_zero j 0 a _

end QuillenTest.FullOpenGradedSectionBassTelescope
