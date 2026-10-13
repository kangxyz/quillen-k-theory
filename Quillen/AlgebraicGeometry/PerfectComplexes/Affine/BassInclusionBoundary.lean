/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassInclusionPasting

/-! # The literal Bass inclusion boundary on the original double cylinders -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable (R : CommRingCat.{u})

/-- The actual target cylinder keeps both original polynomial inclusion tracks. -/
def boundedFlatPerfectBassInclusionTargetTrack :=
  ((boundedFlatPerfectInclusionFlatPullbackHomotopy (polynomialProjection R)).postcomp
    (perfectFlatPrespectrumMap (laurentPlus R))).trans
    ((Homotopy.precomp (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec R))
      (perfectWaldhausen (Spec R)) (boundedFlatPerfectInclusion_exact _))
      (bassSquareHomotopy R)).trans
      ((boundedFlatPerfectInclusionFlatPullbackHomotopy (polynomialProjection R)).symm.postcomp
        (perfectFlatPrespectrumMap (laurentMinus R))))

/-- The three-sided boundary has exactly the association required by the moving square. -/
def boundedFlatPerfectBassInclusionPastedTrack :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPerfectInclusionFlatPullbackHomotopy (laurentPlus R))).trans
    (boundedFlatPerfectBassInclusionTargetTrack R)).trans
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectInclusionFlatPullbackHomotopy (laurentMinus R))).symm

/-- The initial boundary is the unchanged original Bass track followed by actual inclusion. -/
theorem boundedFlatPerfectBassInclusionBoundary_source_level (n : ℕ) :
    ((boundedFlatBassSquareHomotopy R).postcomp (exactOriginalPrespectrumMap
      (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))
      (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
      (boundedFlatPerfectInclusion_exact _))).level n =
      ((boundedFlatPerfectBassInclusionBoundary R).at 0).level n := by
  rw [Homotopy.RelHomotopy.at_zero]
  simp only [boundedFlatBassSquareHomotopy, Homotopy.postcomp_trans, Homotopy.postcomp_symm]
  rfl

/-- The final boundary is the complete actual target Bass cylinder with the prescribed tracks. -/
theorem boundedFlatPerfectBassInclusionBoundary_target_level (n : ℕ) :
    (boundedFlatPerfectBassInclusionPastedTrack R).level n =
      ((boundedFlatPerfectBassInclusionBoundary R).at 1).level n := by
  rw [Homotopy.RelHomotopy.at_one]
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr
    · rfl
    · apply Homotopy.trans_level_congr
      · rfl
      · apply Homotopy.trans_level_congr
        · unfold bassSquareHomotopy
          rw [Homotopy.precomp_trans, Homotopy.precomp_symm]
          rfl
        · exact congrArg (fun H ↦ H.level n)
            (Homotopy.postcomp_symm
              (boundedFlatPerfectInclusionFlatPullbackHomotopy (polynomialProjection R))
              (perfectFlatPrespectrumMap (laurentMinus R)))
  · rfl

/-- The proved geometric boundary yields the entire relative inclusion comparison. -/
def boundedFlatPerfectBassInclusionPasting :
    ((boundedFlatBassSquareHomotopy R).postcomp (exactOriginalPrespectrumMap
      (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))
      (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
      (boundedFlatPerfectInclusion_exact _))).RelHomotopy
      (boundedFlatPerfectBassInclusionPastedTrack R) :=
  Homotopy.RelHomotopy.ofLevels (boundedFlatPerfectBassInclusionBoundary R) _ _
    (by intro n; simpa only [Homotopy.RelHomotopy.at_zero] using
      boundedFlatPerfectBassInclusionBoundary_source_level R n)
    (by intro n; simpa only [Homotopy.RelHomotopy.at_one] using
      boundedFlatPerfectBassInclusionBoundary_target_level R n)

/-- Regroup the original source endpoints for literal pushout descent. -/
def boundedFlatPerfectBassInclusionSourceDescTrack :=
  ((boundedFlatBassSquareHomotopy R).postcomp (exactOriginalPrespectrumMap
    (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))
    (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
    (boundedFlatPerfectInclusion_exact _))).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Regroup the actual target endpoints for the original polynomial span comparison. -/
def boundedFlatPerfectBassInclusionTargetDescTrack :=
  (boundedFlatPerfectBassInclusionTargetTrack R).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- The complete pasted boundary on the untransported Laurent inclusion precompositions. -/
def boundedFlatPerfectBassInclusionPastedDescTrack :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPerfectInclusionFlatPullbackHomotopy (laurentPlus R))).trans
    (boundedFlatPerfectBassInclusionTargetDescTrack R)).trans
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectInclusionFlatPullbackHomotopy (laurentMinus R))).symm

/-- The original geometric inclusion boundary in the exact moving-descent interface. -/
def boundedFlatPerfectBassInclusionDescPasting :
    (boundedFlatPerfectBassInclusionSourceDescTrack R).RelHomotopy
      (boundedFlatPerfectBassInclusionPastedDescTrack R) :=
  Homotopy.RelHomotopy.ofLevels (boundedFlatPerfectBassInclusionPasting R) _ _ (fun _ ↦ rfl)
    (by
      intro n
      apply Homotopy.trans_level_congr
      · apply Homotopy.trans_level_congr <;> rfl
      · rfl)

end Quillen.PerfectComplexes
