/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.RelativeHomotopyPasting
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NormalizedPullbackCoherence

/-! The genuine geometric three-map comparison in the reversed-edge Bass-square orientation. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes Quillen.LoopPrespectrum
universe u
namespace Quillen.Tests.NormalizedPullbackRotation

/-- Actual arbitrary-scheme-map associativity supplies the rotated whole-track comparison. -/
def originalTripleRotation {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :=
  Homotopy.RelHomotopy.rotate (boundedFlatNormalizedTriplePasting f g h)

/-- Rotation fixes the actual chosen basepoint throughout both independent homotopy times. -/
theorem zero_line {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (n : ℕ) (r s : unitInterval) :
    (originalTripleRotation f g h).level n
      (r, (s, (Quillen.Waldhausen.IteratedS.originalPrespectrum
        (boundedFlatPerfectWaldhausen T)).point n)) =
      (Quillen.Waldhausen.IteratedS.originalPrespectrum
        (boundedFlatPerfectWaldhausen X)).point n :=
  ((originalTripleRotation f g h).at r).at_point n s

end Quillen.Tests.NormalizedPullbackRotation
