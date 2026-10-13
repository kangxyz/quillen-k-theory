/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SquareTrackOriginal

/-! Identify the common outer projection in the genuine double-square comparison. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes.DoubleSquareTrack
variable {A B C A' B' C' : Scheme.{u}}
  (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
  (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
  (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
  (r : C ⟶ A) (r' : C' ⟶ A') (hr : q ≫ p = r) (hr' : q' ≫ p' = r')

include hp hq hr hr' in
/-- The actual two chart squares induce the square between their common projections. -/
theorem outer_eq : c ≫ r = r' ≫ a := by
  rw [← hr, ← hr']
  exact (total_eq p q p' q' a b c hp hq).symm

/-- The original source chart composition, transported to the common projection. -/
def sourceProjection :=
  (boundedFlatPerfectPrespectrumCompHomotopy q p).cast
    (congrArg boundedFlatPerfectPrespectrumMap hr) rfl

/-- The original target chart composition, transported to the common projection. -/
def targetProjection :=
  (boundedFlatPerfectPrespectrumCompHomotopy q' p').cast
    (congrArg boundedFlatPerfectPrespectrumMap hr') rfl

/-- The entire actual outer square of common projections. -/
def outerProjectionSquare :=
  boundedFlatPerfectPrespectrumSquareHomotopy c r r' a
    (outer_eq p q p' q' a b c hp hq r r' hr hr')

/-- The outer route retains both original chart composition tracks and the common square. -/
def reducedRight :=
  ((sourceProjection p q r hr).postcomp (boundedFlatPerfectPrespectrumMap c)).symm.trans
    ((outerProjectionSquare p q p' q' a b c hp hq r r' hr hr').trans
      ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap a)
        (targetProjection p' q' r' hr')).cast rfl (Category.assoc _ _ _).symm))

/-- Projection identification preserves every point of the actual outer square track. -/
theorem outerProjectionSquare_level (n : ℕ) :
    (outerProjectionSquare p q p' q' a b c hp hq r r' hr hr').level n =
      (boundedFlatPerfectPrespectrumSquareHomotopy c (q ≫ p) (q' ≫ p') a
        (total_eq p q p' q' a b c hp hq).symm).level n := by
  unfold outerProjectionSquare
  rw [boundedFlatPerfectPrespectrumSquareHomotopy_level,
    boundedFlatPerfectPrespectrumSquareHomotopy_level]
  apply Homotopy.trans_level_congr
  · apply ContinuousMap.ext
    rintro ⟨s, x⟩
    change (boundedFlatPerfectPrespectrumCompHomotopy c r).level n (unitInterval.symm s, x) =
      (boundedFlatPerfectPrespectrumCompHomotopy c (q ≫ p)).level n (unitInterval.symm s, x)
    exact DFunLike.congr_fun
      (congrArg (fun k ↦ (boundedFlatPerfectPrespectrumCompHomotopy c k).level n) hr.symm) _
  · change (boundedFlatPerfectPrespectrumCompHomotopy r' a).level n =
      (boundedFlatPerfectPrespectrumCompHomotopy (q' ≫ p') a).level n
    exact congrArg (fun k ↦ (boundedFlatPerfectPrespectrumCompHomotopy k a).level n) hr'.symm

/-- The reduced outer route preserves the full previously constructed comparison boundary. -/
theorem reducedRight_level (n : ℕ) :
    (reducedRight p q p' q' a b c hp hq r r' hr hr').level n =
      (originalRight p q p' q' a b c hp hq).level n := by
  apply Homotopy.trans_level_congr
  · apply Homotopy.symm_level_congr
    apply Homotopy.postcomp_level_congr
    rfl
  · apply Homotopy.trans_level_congr
    · exact outerProjectionSquare_level p q p' q' a b c hp hq r r' hr hr' n
    · apply Homotopy.precomp_level_congr
      rfl

/-- Genuine double-square pasting through a specified common projection, using only geometry. -/
def projectionComparison :
    (originalLeft p q p' q' a b c hp hq).RelHomotopy
      (reducedRight p q p' q' a b c hp hq r r' hr hr') :=
  Homotopy.RelHomotopy.ofLevels (originalComparison p q p' q' a b c hp hq) _ _
    (fun _ ↦ rfl) (reducedRight_level p q p' q' a b c hp hq r r' hr hr')

end Quillen.PerfectComplexes.DoubleSquareTrack
