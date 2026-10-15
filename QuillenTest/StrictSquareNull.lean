/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.StrictSquareNull

/-! Consumer checks for the original source nullhomotopy, its based endpoints, and strict
naturality at every time slice. The source, cone and maps are the actual constructions. -/
@[expose] public section

open Quillen.LoopPrespectrum
open Quillen.LoopPrespectrum.StrictSquare


noncomputable section
open CategoryTheory
open scoped unitInterval
universe u
namespace QuillenTest.StrictSquareNull

open Quillen
open LoopPrespectrum
open LoopPrespectrum.StrictSquare

variable (S : Arrow (Arrow LoopPrespectrum.{u}))

/-- At the cylinder bottom the original two-leg composite enters the actual cone. -/
theorem originalBottom (n : ℕ) (x : S.left.left.space n) :
    (sourceNullHomotopy S).level n (0, x) =
      (mappingConeInclusion (comparison S)).map n
        (S.hom.right.map n (S.left.hom.map n x)) :=
  (sourceNullHomotopy S).at_zero n x

/-- The original cone top and the based line are collapsed at the same actual cone point. -/
theorem collapsedTopAndBase (n : ℕ) (s : unitInterval) (x : S.left.left.space n) :
    (sourceNullHomotopy S).level n (1, x) = (mappingCone (comparison S)).point n ∧
      (sourceNullHomotopy S).level n (s, S.left.left.point n) =
        (mappingCone (comparison S)).point n :=
  ⟨(sourceNullHomotopy S).at_one n x, (sourceNullHomotopy S).at_point n s⟩

/-- Cone time remains independent from structure time on the original source nullhomotopy. -/
theorem independentParameters (n : ℕ) (s t : unitInterval) (x : S.left.left.space n) :
    (sourceNullHomotopy S).level (n + 1) (s, S.left.left.structureMap n x t) =
      (mappingCone (comparison S)).structureMap n ((sourceNullHomotopy S).level n (s, x)) t :=
  (sourceNullHomotopy S).comm n s x t

variable {S T : Arrow (Arrow LoopPrespectrum.{u})}

/-- Strict coefficient naturality holds as an equality of genuine prespectrum time slices. -/
theorem timeSliceNaturality (a : S ⟶ T) (s : unitInterval) :
    (sourceNullHomotopy S).at s ≫ mappingConeMap (strictSquareComparisonFunctor.map a) =
      a.left.left ≫ (sourceNullHomotopy T).at s := by
  apply Hom.ext
  funext n
  ext x
  exact sourceNullHomotopy_naturality_apply a n s x

/-- Whole-homotopy naturality specializes to the same literal point equality. -/
theorem wholeTrackNaturality (a : S ⟶ T) (n : ℕ) (z : unitInterval × S.left.left.space n) :
    (((sourceNullHomotopy S).postcomp
      (mappingConeMap (strictSquareComparisonFunctor.map a))).cast
        (sourceNullHomotopy_start_naturality a) (sourceNullHomotopy_end_naturality a)).level n z =
      ((sourceNullHomotopy T).precomp a.left.left).level n z := by
  exact congrArg (fun H ↦ H.level n z) (sourceNullHomotopy_naturality a)

end QuillenTest.StrictSquareNull
