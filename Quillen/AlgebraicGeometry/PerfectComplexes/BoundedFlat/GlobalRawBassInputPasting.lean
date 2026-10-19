/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputCharts
public import Quillen.Topology.Prespectrum.RelativeHomotopySquarePasting
public import Quillen.Topology.Prespectrum.HomotopySquareOfPasting

/-!
# The original global raw Bass input overlap

The actual positive and inverse chart pastings give the complete relative overlap comparison
for a scheme arrow. Both original chart paths and the polynomial cylinder are retained.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalRawBass
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The two genuine Laurent scheme-arrow pastings cancel their common outer square and give
an actual relative boundary comparison, retaining the prescribed concatenation associations. -/
def inputBoundary :=
  Homotopy.RelHomotopy.pasteTwoSquares
    (plusInputPasting g) (minusInputPasting g)

/-- The right-associated target cylinder retains both original polynomial-square tracks. -/
def inputTargetTrack :=
  ((polynomialSquareHomotopy g).postcomp
    (boundedFlatPerfectPrespectrumMap (plus.app X))).trans
    (((Homotopy.precomp (boundedFlatPerfectPrespectrumMap g)
      (squareHomotopy X)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
      ((polynomialSquareHomotopy g).symm.postcomp
        (boundedFlatPerfectPrespectrumMap (minus.app X))))

/-- The precise outer left association required by the moving-square conversion. -/
def inputPastedTrack :=
  (((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (projection.app Y))
    (plusSquareHomotopy g)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    (inputTargetTrack g)).trans
    ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (projection.app Y))
      (minusSquareHomotopy g)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).symm

/-- The initial boundary is the entire original Bass square under scheme change. -/
theorem inputBoundary_source_level (n : ℕ) :
    ((squareHomotopy Y).postcomp
      (boundedFlatPerfectPrespectrumMap (laurent.map g))).level
        n =
      ((inputBoundary g).at 0).level n := by
  rw [Homotopy.RelHomotopy.at_zero]
  simp only [squareHomotopy, Homotopy.postcomp_trans,
    Homotopy.postcomp_symm]

/-- The constructed boundary ends at the original Bass target cylinder with exact associations. -/
theorem inputBoundary_target_level (n : ℕ) :
    (inputPastedTrack g).level n =
      ((inputBoundary g).at 1).level n := by
  rw [Homotopy.RelHomotopy.at_one]
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr
    · rfl
    · apply Homotopy.trans_level_congr
      · rfl
      · apply Homotopy.trans_level_congr
        · unfold squareHomotopy
          rw [Homotopy.precomp_trans, Homotopy.precomp_symm]
          apply Homotopy.trans_level_congr
          · apply Homotopy.symm_level_congr
            rfl
          · rfl
        · exact congrArg (fun H ↦ H.level n)
            (Homotopy.postcomp_symm (polynomialSquareHomotopy g)
              (boundedFlatPerfectPrespectrumMap (minus.app X)))
  · rfl

/-- The original Bass square satisfies the actual scheme-arrow pasted-track relation. -/
def inputPasting :
    ((squareHomotopy Y).postcomp
      (boundedFlatPerfectPrespectrumMap (laurent.map g))).RelHomotopy
      (inputPastedTrack g) :=
  Homotopy.RelHomotopy.ofLevels (inputBoundary g) _ _
    (by intro n; simpa only [Homotopy.RelHomotopy.at_zero] using
      inputBoundary_source_level g n)
    (by intro n; simpa only [Homotopy.RelHomotopy.at_one] using
      inputBoundary_target_level g n)

/-- Regroup the source endpoint maps to the literal span-comparison composition maps. -/
def inputSourceDescTrack :=
  ((squareHomotopy Y).postcomp
    (boundedFlatPerfectPrespectrumMap (laurent.map g))).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Regroup the target endpoints to the literal polynomial-scheme composite maps. -/
def inputTargetDescTrack :=
  (inputTargetTrack g).cast (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- The exact boundary now uses the untransported precompositions of both Laurent squares. -/
def inputPastedDescTrack :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (projection.app Y))
    (plusSquareHomotopy g)).trans
      (inputTargetDescTrack g)).trans
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (projection.app Y))
      (minusSquareHomotopy g)).symm

/-- The genuine geometric boundary filler in the exact moving-pushout descent interface. -/
def inputDescPasting :
    (inputSourceDescTrack g).RelHomotopy
      (inputPastedDescTrack g) :=
  Homotopy.RelHomotopy.ofLevels (inputPasting g) _ _ (fun _ ↦ rfl)
    (by
      intro n
      apply Homotopy.trans_level_congr
      · apply Homotopy.trans_level_congr <;> rfl
      · apply Homotopy.symm_level_congr
        rfl)

end Quillen.PerfectComplexes.GlobalRawBass
