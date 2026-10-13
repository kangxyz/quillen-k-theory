/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedFlatBassNullTrack

/-! The actual moving comparison between the two original Bass Laurent nullhomotopies. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The genuine original-null comparison has the exact fixed-zero three-sided boundary. -/
def boundedFlatBassLaurentNullCoefficientBoundary :
    (BassNullTrack.originalOldNull f).RelHomotopy
      (((BassNullTrack.laurentMovement f).trans (BassNullTrack.originalNewNull f)).trans
        (Quillen.LoopPrespectrum.Homotopy.refl (zeroHom
          (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R)))
          (mappingCone (boundedFlatBassSquareComparison S)))).symm) := by
  have J := (BassNullTrack.originalNullComparison f).trans
    (Homotopy.RelHomotopy.transRefl
      ((BassNullTrack.laurentMovement f).trans (BassNullTrack.originalNewNull f))).symm
  exact J.ofLevels _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- Arbitrary coefficient change gives a genuine moving square of the original nullhomotopies. -/
def boundedFlatBassLaurentNullCoefficientSquare :
    (BassNullTrack.originalOldNull f).Square (BassNullTrack.originalNewNull f)
      (BassNullTrack.laurentMovement f)
      (Quillen.LoopPrespectrum.Homotopy.refl (zeroHom
        (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R)))
        (mappingCone (boundedFlatBassSquareComparison S)))) :=
  (boundedFlatBassLaurentNullCoefficientBoundary f).toSquare

end Quillen.PerfectComplexes
