/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.InclusionCompositionTrack
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassConeComparison
public import Quillen.Topology.Prespectrum.RelativeHomotopySquarePasting

/-!
# The actual geometric inclusion pasting for both Laurent charts

The original bounded-flat-to-perfect inclusion normalization tracks are compatible with the
geometric plus and minus chart composition tracks. Both comparisons use their literal Laurent
projection; canceling the common outer track produces the whole Bass cylinder boundary.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open Quillen.Scheme.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes

private theorem perfectFlatPrespectrumMap_congr {X Y : Scheme.{u}} {f g : X ⟶ Y}
    [Flat f] [Flat g] (e : f = g) :
    perfectFlatPrespectrumMap f = perfectFlatPrespectrumMap g := by
  subst g
  rfl

private theorem transportedHomotopy_eq_cast {E F : LoopPrespectrum.{u}}
    {a a' b b' : E ⟶ F} (ea : a = a') (eb : b = b')
    (p : Homotopy a b = Homotopy a' b') (H : Homotopy a b) :
    p.mp H = H.cast ea eb := by
  subst a'
  subst b'
  rfl

/-- The original perfect positive chart track is exactly the literal endpoint cast. -/
theorem laurentPlusHomotopy_eq_cast (R : CommRingCat.{u}) :
    laurentPlusHomotopy R =
      (perfectFlatPrespectrumCompHomotopy (laurentPlus R) (polynomialProjection R)).cast
        (by simp only [laurentPlus_projection]) rfl := by
  unfold laurentPlusHomotopy
  exact transportedHomotopy_eq_cast
    (perfectFlatPrespectrumMap_congr (laurentPlus_projection R)) rfl _ _

/-- The separate original perfect negative chart track is exactly its own endpoint cast. -/
theorem laurentMinusHomotopy_eq_cast (R : CommRingCat.{u}) :
    laurentMinusHomotopy R =
      (perfectFlatPrespectrumCompHomotopy (laurentMinus R) (polynomialProjection R)).cast
        (by simp only [laurentMinus_projection]) rfl := by
  unfold laurentMinusHomotopy
  exact transportedHomotopy_eq_cast
    (perfectFlatPrespectrumMap_congr (laurentMinus_projection R)) rfl _ _

/-- The plus inclusion route before the common outer geometric track is canceled. -/
def boundedFlatPerfectPlusInclusionLeftTrack (R : CommRingCat.{u}) :=
  (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPerfectInclusionFlatPullbackHomotopy (laurentPlus R))).trans
    ((boundedFlatPerfectInclusionFlatPullbackHomotopy (polynomialProjection R)).postcomp
      (perfectFlatPrespectrumMap (laurentPlus R)))

/-- The minus inclusion route keeps its own inverse-coordinate geometric track. -/
def boundedFlatPerfectMinusInclusionLeftTrack (R : CommRingCat.{u}) :=
  (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection R))
    (boundedFlatPerfectInclusionFlatPullbackHomotopy (laurentMinus R))).trans
    ((boundedFlatPerfectInclusionFlatPullbackHomotopy (polynomialProjection R)).postcomp
      (perfectFlatPrespectrumMap (laurentMinus R)))

/-- The plus route through the literal Laurent projection inclusion track. -/
def boundedFlatPerfectPlusInclusionRightTrack (R : CommRingCat.{u}) :=
  ((boundedFlatLaurentPlusHomotopy R).postcomp (exactOriginalPrespectrumMap
    (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))
    (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
    (boundedFlatPerfectInclusion_exact _))).symm.trans
    ((boundedFlatPerfectInclusionFlatPullbackHomotopy (laurentProjection R)).trans
      (Homotopy.precomp (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec R))
        (perfectWaldhausen (Spec R)) (boundedFlatPerfectInclusion_exact _))
        (laurentPlusHomotopy R)))

/-- The minus route through the same literal Laurent projection inclusion track. -/
def boundedFlatPerfectMinusInclusionRightTrack (R : CommRingCat.{u}) :=
  ((boundedFlatLaurentMinusHomotopy R).postcomp (exactOriginalPrespectrumMap
    (boundedFlatPerfectWaldhausen (Spec (.of (LaurentPolynomial R))))
    (perfectWaldhausen (Spec (.of (LaurentPolynomial R))))
    (boundedFlatPerfectInclusion_exact _))).symm.trans
    ((boundedFlatPerfectInclusionFlatPullbackHomotopy (laurentProjection R)).trans
      (Homotopy.precomp (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen (Spec R))
        (perfectWaldhausen (Spec R)) (boundedFlatPerfectInclusion_exact _))
        (laurentMinusHomotopy R)))

/-- The actual normalized inclusion respects the original positive geometric chart pasting. -/
def boundedFlatPerfectPlusInclusionPasting (R : CommRingCat.{u}) :
    (boundedFlatPerfectPlusInclusionLeftTrack R).RelHomotopy
      (boundedFlatPerfectPlusInclusionRightTrack R) := by
  apply Homotopy.RelHomotopy.ofLevels
    (boundedFlatPerfectInclusionCompositionPasting (laurentPlus R) (polynomialProjection R))
  · intro n
    rfl
  · intro n
    apply Homotopy.trans_level_congr
    · apply Homotopy.symm_level_congr
      apply Homotopy.postcomp_level_congr
      rfl
    · apply Homotopy.trans_level_congr
      · exact boundedFlatPerfectInclusionFlatPullbackHomotopy_level_congr
          (laurentPlus_projection R).symm n
      · apply Homotopy.precomp_level_congr
        rw [laurentPlusHomotopy_eq_cast]
        rfl

/-- The actual normalized inclusion independently respects the inverse-coordinate chart pasting. -/
def boundedFlatPerfectMinusInclusionPasting (R : CommRingCat.{u}) :
    (boundedFlatPerfectMinusInclusionLeftTrack R).RelHomotopy
      (boundedFlatPerfectMinusInclusionRightTrack R) := by
  apply Homotopy.RelHomotopy.ofLevels
    (boundedFlatPerfectInclusionCompositionPasting (laurentMinus R) (polynomialProjection R))
  · intro n
    rfl
  · intro n
    apply Homotopy.trans_level_congr
    · apply Homotopy.symm_level_congr
      apply Homotopy.postcomp_level_congr
      rfl
    · apply Homotopy.trans_level_congr
      · exact boundedFlatPerfectInclusionFlatPullbackHomotopy_level_congr
          (laurentMinus_projection R).symm n
      · apply Homotopy.precomp_level_congr
        rw [laurentMinusHomotopy_eq_cast]
        rfl

/-- Both original chart pastings give the actual Bass boundary after canceling their common
Laurent inclusion track through its whole reverse-track contraction. -/
def boundedFlatPerfectBassInclusionBoundary (R : CommRingCat.{u}) :=
  Homotopy.RelHomotopy.pasteTwoSquares
    (boundedFlatPerfectPlusInclusionPasting R) (boundedFlatPerfectMinusInclusionPasting R)

end Quillen.PerfectComplexes
