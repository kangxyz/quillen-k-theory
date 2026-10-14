/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.DoubleSquareRectangleNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SquareTrackOriginal

/-! The unchanged exported original square tracks retain the same whole scalar rectangle. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Convexity
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.DoubleSquareScalarPaths
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)

/-- The full native `ofLevels` transport identifies the same scalar rectangle with both
original exported geometric square tracks, at every level and both times. -/
theorem original_rectangle_nativeLift :
    HomotopyLift (DoubleSquareMergedSimplex.simplex p q p' q' a b c hp hq)
      rectangleParameter (DoubleSquareTrack.originalComparison p q p' q' a b c hp hq) := by
  intro n r s x
  exact rectangle_native p q p' q' a b c hp hq n r s x

end Quillen.PerfectComplexes.DoubleSquareScalarPaths
