/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassInclusionBoundary
public import Quillen.Topology.Prespectrum.HomotopySquareOfPasting
public import Quillen.Topology.Prespectrum.PushoutMovingHomotopy

/-!
# The actual bounded-flat-to-perfect Bass comparison homotopy

The proved geometric inclusion boundary descends to the original reduced double cylinders.
The endpoints are the unchanged original Bass comparison and original inclusion span map.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable (R : CommRingCat.{u})

/-- The target track is the literal original inclusion span cylinder followed by Bass comparison. -/
theorem boundedFlatPerfectBassInclusionTargetDescTrack_level (n : ℕ) :
    (boundedFlatPerfectBassInclusionTargetDescTrack R).level n =
      ((HomotopyPushout.mapSquareHomotopy
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (perfectFlatPrespectrumMap (polynomialProjection R))
        (perfectFlatPrespectrumMap (polynomialProjection R))
        (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec R))
          (perfectWaldhausen (Spec R)) (boundedFlatPerfectInclusion_exact _))
        (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec (.of (Polynomial R))))
          (perfectWaldhausen (Spec (.of (Polynomial R)))) (boundedFlatPerfectInclusion_exact _))
        (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec (.of (Polynomial R))))
          (perfectWaldhausen (Spec (.of (Polynomial R)))) (boundedFlatPerfectInclusion_exact _))
        (boundedFlatPerfectInclusionFlatPullbackHomotopy (polynomialProjection R))
        (boundedFlatPerfectInclusionFlatPullbackHomotopy (polynomialProjection R))).postcomp
          (bassSquareComparison R)).level n := by
  simp only [boundedFlatPerfectBassInclusionTargetDescTrack, Homotopy.cast_level,
    boundedFlatPerfectBassInclusionTargetTrack, HomotopyPushout.mapSquareHomotopy,
    Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr <;> rfl

/-- The source descent is the literal original bounded-flat Bass map followed by inclusion. -/
theorem boundedFlatPerfectBassInclusionSourceDesc_eq :
    HomotopyPushout.desc
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (laurentPlus R) ≫ exactOriginalPrespectrumMap
        (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (boundedFlatPerfectInclusion_exact _))
      (boundedFlatPerfectPrespectrumMap (laurentMinus R) ≫ exactOriginalPrespectrumMap
        (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
        (boundedFlatPerfectInclusion_exact _))
      (boundedFlatPerfectBassInclusionSourceDescTrack R) =
    boundedFlatBassSquareComparison R ≫ exactOriginalPrespectrumMap
      (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))
      (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
      (boundedFlatPerfectInclusion_exact _) := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    rfl

/-- The target descent is the actual inclusion pushout map followed by original perfect Bass. -/
theorem boundedFlatPerfectBassInclusionTargetDesc_eq :
    HomotopyPushout.desc
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
      (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (Spec (.of (Polynomial R)))) (boundedFlatPerfectInclusion_exact _) ≫
        perfectFlatPrespectrumMap (laurentPlus R))
      (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec (.of (Polynomial R))))
        (perfectWaldhausen (Spec (.of (Polynomial R)))) (boundedFlatPerfectInclusion_exact _) ≫
        perfectFlatPrespectrumMap (laurentMinus R))
      (boundedFlatPerfectBassInclusionTargetDescTrack R) =
    boundedFlatPerfectFlatPullbackPushoutMap (polynomialProjection R) (polynomialProjection R) ≫
      bassSquareComparison R := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    exact DFunLike.congr_fun (boundedFlatPerfectBassInclusionTargetDescTrack_level R n) (s, x)

/-- The proved original geometric square supplies the complete Bass comparison homotopy.
In particular the cone comparison needs no further compatibility premise. -/
def boundedFlatPerfectBassComparisonHomotopy :
    Homotopy (boundedFlatBassSquareComparison R ≫ exactOriginalPrespectrumMap
      (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))
      (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
      (boundedFlatPerfectInclusion_exact _))
    (boundedFlatPerfectFlatPullbackPushoutMap (polynomialProjection R) (polynomialProjection R) ≫
      bassSquareComparison R) :=
  (HomotopyPushout.descSquareHomotopy
    (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPerfectInclusionFlatPullbackHomotopy (laurentPlus R))
    (boundedFlatPerfectInclusionFlatPullbackHomotopy (laurentMinus R))
    (boundedFlatPerfectBassInclusionDescPasting R).toSquare).cast
      (boundedFlatPerfectBassInclusionSourceDesc_eq R)
      (boundedFlatPerfectBassInclusionTargetDesc_eq R)

/-- The original positive chart inclusion track is retained at every left endpoint. -/
theorem boundedFlatPerfectBassComparisonHomotopy_inl (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (Spec (.of (Polynomial R))))).space n) :
    (boundedFlatPerfectBassComparisonHomotopy R).level n
      (r, (HomotopyPushout.inl (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))).map n x) =
      (boundedFlatPerfectInclusionFlatPullbackHomotopy (laurentPlus R)).level n (r, x) := rfl

/-- The separate inverse-coordinate inclusion track is retained at every right endpoint. -/
theorem boundedFlatPerfectBassComparisonHomotopy_inr (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (Spec (.of (Polynomial R))))).space n) :
    (boundedFlatPerfectBassComparisonHomotopy R).level n
      (r, (HomotopyPushout.inr (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R))).map n x) =
      (boundedFlatPerfectInclusionFlatPullbackHomotopy (laurentMinus R)).level n (r, x) := rfl

/-- The comparison on the entire original cylinder is the proved moving geometric square. -/
theorem boundedFlatPerfectBassComparisonHomotopy_cylinder (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatPerfectBassComparisonHomotopy R).level n
      (r, HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) n (s, x)) =
      (boundedFlatPerfectBassInclusionDescPasting R).toSquare.level n (r, (s, x)) := rfl

/-- Pulling back the actual cylinder square recovers every original relative-pasting parameter. -/
theorem boundedFlatPerfectBassComparisonHomotopy_collapse (n : ℕ)
    (z : unitInterval × unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (Spec R))).space n) :
    (boundedFlatPerfectBassComparisonHomotopy R).level n
      ((Quillen.ThreeSideSquare.collapse z).1,
        HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection R)) n
          ((Quillen.ThreeSideSquare.collapse z).2, x)) =
      (boundedFlatPerfectBassInclusionDescPasting R).level n (z.1, (z.2, x)) :=
  (boundedFlatPerfectBassInclusionDescPasting R).toSquare_collapse n z x

end Quillen.PerfectComplexes
