/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Coefficients.Naturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSectionEvaluationSourceLeg
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SquareTrackProjection
public import Quillen.Topology.Prespectrum.RelativeHomotopySquarePasting
public import Quillen.Topology.Prespectrum.HomotopySquareOfPasting
public import Quillen.Topology.Prespectrum.PushoutMovingHomotopy
public import Quillen.Topology.Prespectrum.ConeHomotopySquare

/-!
# Original raw Bass maps on arbitrary coefficient fibers

For `P : Over (Spec R)` and each original coefficient arrow `u : a ⟶ b`, this module
constructs the two polynomial-span maps, the whole original Laurent comparison square,
its quotient-cone map and the parameter-looped map on the original one-step raw objects.
The chart, cylinder, cone-inclusion and positive-source-leg equations retain the original
maps and their independent parameters.

These constructions extend the affine source family `Affine/BoundedFlatBassSpanMap`,
`BoundedFlatBassPasting`, `BoundedFlatBassBoundary` and `BoundedFlatBassStepMap` at revision
`83629578a3d70787d41ec631f5234af8758716af` to the actual fibers `space (op P, a)`.
The native triple, rectangle and projection comparisons are used from their existing
owners. Coefficient identity/composition, full null/seed/evaluation naturality and higher
raw iteration remain separate obligations.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

open Quillen


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R))

variable {a b : Under R} (u : a ⟶ b)

/-- This is the original polynomial square, with its actual arbitrary-map bounded-flat pullbacks. -/
def boundedFlatCoefficientPolynomialSquareHomotopy : Homotopy
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a) ≫
      boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P u) ≫
      boundedFlatPerfectPrespectrumMap (polynomialProjection P b)) :=
  boundedFlatPerfectPrespectrumSquareHomotopy _ _ _ _
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
    (polynomialUnderCoefficient R) u)

/-- Arbitrary coefficient change supplies an actual map of the two polynomial-chart pushouts. -/
def boundedFlatCoefficientPolynomialSpanMap :
    HomotopyPushout.prespectrum (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) ⟶
      HomotopyPushout.prespectrum (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P b)) :=
  HomotopyPushout.mapOfHomotopies _ _ _ _ (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
    (boundedFlatCoefficientPolynomialSquareHomotopy P u)
      (boundedFlatCoefficientPolynomialSquareHomotopy P u)

/-- The original left polynomial-chart endpoint is retained literally. -/
@[simp]
lemma inl_boundedFlatCoefficientPolynomialSpanMap :
    HomotopyPushout.inl _ _ ≫ boundedFlatCoefficientPolynomialSpanMap P u =
      boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
        HomotopyPushout.inl _ _ :=
  HomotopyPushout.inl_mapOfHomotopies _ _ _ _ _ _ _ _ _

/-- The original right polynomial-chart endpoint is retained literally. -/
@[simp]
lemma inr_boundedFlatCoefficientPolynomialSpanMap :
    HomotopyPushout.inr _ _ ≫ boundedFlatCoefficientPolynomialSpanMap P u =
      boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
        HomotopyPushout.inr _ _ :=
  HomotopyPushout.inr_mapOfHomotopies _ _ _ _ _ _ _ _ _

/-- Every cylinder point retains the original pasted geometric comparison tracks. -/
lemma boundedFlatCoefficientPolynomialSpanMap_cylinder (n : ℕ) (s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientPolynomialSpanMap P u).map n
        (HomotopyPushout.cylinder (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (s, x)) =
      (HomotopyPushout.mapSquareHomotopy _ _ _ _ (boundedFlatPerfectPrespectrumMap (coefficientMap
        P u))
        (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
        (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
        (boundedFlatCoefficientPolynomialSquareHomotopy P u)
          (boundedFlatCoefficientPolynomialSquareHomotopy P u)).level n
          (s, x) := rfl

/-- The positive Laurent chart retains its actual geometric square. -/
def boundedFlatCoefficientPlusSquareHomotopy : Homotopy
    (boundedFlatPerfectPrespectrumMap (laurentPlus P a) ≫
      boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
      boundedFlatPerfectPrespectrumMap (laurentPlus P b)) :=
  boundedFlatPerfectPrespectrumSquareHomotopy _ _ _ _
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
    (underToLaurent R) u)

/-- The inverse-coordinate Laurent chart retains its actual geometric square. -/
def boundedFlatCoefficientMinusSquareHomotopy : Homotopy
    (boundedFlatPerfectPrespectrumMap (laurentMinus P a) ≫
      boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
      boundedFlatPerfectPrespectrumMap (laurentMinus P b)) :=
  boundedFlatPerfectPrespectrumSquareHomotopy _ _ _ _
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
    (underToLaurentInvert R) u)



/-- The original outer Laurent projection square is common to both chart diagrams. -/
def boundedFlatCoefficientLaurentSquareHomotopy :=
  boundedFlatPerfectPrespectrumSquareHomotopy (coefficientMap P ((laurentUnderFunctor R).map u))
    (laurentProjection P a) (laurentProjection P b) (coefficientMap P u)
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
        (laurentUnderCoefficient R) u)

/-- Paste the original plus Laurent square and the original polynomial square. -/
def boundedFlatCoefficientPlusLeftTrack :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientPlusSquareHomotopy P u)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((boundedFlatCoefficientPolynomialSquareHomotopy P u).postcomp
      (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))

/-- The plus route through the common original Laurent projection square. -/
def boundedFlatCoefficientPlusRightTrack :=
  ((boundedFlatCoefficientLaurentPlusHomotopy P a).postcomp
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map
      u)))).symm.trans
    ((boundedFlatCoefficientLaurentSquareHomotopy P u).trans
      ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
        (boundedFlatCoefficientLaurentPlusHomotopy P b)).cast rfl (Category.assoc _ _ _).symm))

/-- Genuine geometric pasting for the original plus coefficient tracks and common outer square. -/
def boundedFlatCoefficientPlusPasting :
    (boundedFlatCoefficientPlusLeftTrack P u).RelHomotopy
      (boundedFlatCoefficientPlusRightTrack P u) :=
  DoubleSquareTrack.projectionComparison (polynomialProjection P a) (laurentPlus P a)
    (polynomialProjection P b) (laurentPlus P b) (coefficientMap P u)
    (coefficientMap P ((polynomialUnderFunctor R).map u)) (coefficientMap P ((laurentUnderFunctor
      R).map u))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (polynomialUnderCoefficient R) u)
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P (underToLaurent
        R) u)
    (laurentProjection P a) (laurentProjection P b)
    (laurentPlus_projection P a) (laurentPlus_projection P b)

/-- Paste the original minus Laurent square and the original polynomial square. -/
def boundedFlatCoefficientMinusLeftTrack :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientMinusSquareHomotopy P u)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((boundedFlatCoefficientPolynomialSquareHomotopy P u).postcomp
      (boundedFlatPerfectPrespectrumMap (laurentMinus P b)))

/-- The minus route through the common original Laurent projection square. -/
def boundedFlatCoefficientMinusRightTrack :=
  ((boundedFlatCoefficientLaurentMinusHomotopy P a).postcomp
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map
      u)))).symm.trans
    ((boundedFlatCoefficientLaurentSquareHomotopy P u).trans
      ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
        (boundedFlatCoefficientLaurentMinusHomotopy P b)).cast rfl (Category.assoc _ _ _).symm))

/-- Genuine geometric pasting for the original minus coefficient tracks and common outer square. -/
def boundedFlatCoefficientMinusPasting :
    (boundedFlatCoefficientMinusLeftTrack P u).RelHomotopy
      (boundedFlatCoefficientMinusRightTrack P u) :=
  DoubleSquareTrack.projectionComparison (polynomialProjection P a) (laurentMinus P a)
    (polynomialProjection P b) (laurentMinus P b) (coefficientMap P u)
    (coefficientMap P ((polynomialUnderFunctor R).map u)) (coefficientMap P ((laurentUnderFunctor
      R).map u))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (polynomialUnderCoefficient R) u)
      (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
        (underToLaurentInvert R) u)
    (laurentProjection P a) (laurentProjection P b)
    (laurentMinus_projection P a) (laurentMinus_projection P b)

/-- The two genuine Laurent coefficient pastings cancel their common outer square and give
an actual relative boundary comparison, retaining the prescribed concatenation associations. -/
def boundedFlatCoefficientBassBoundary :=
  Homotopy.RelHomotopy.pasteTwoSquares
    (boundedFlatCoefficientPlusPasting P u) (boundedFlatCoefficientMinusPasting P u)



/-- The right-associated target cylinder retains both original polynomial-square tracks. -/
def boundedFlatCoefficientBassTargetTrack :=
  ((boundedFlatCoefficientPolynomialSquareHomotopy P u).postcomp
    (boundedFlatPerfectPrespectrumMap (laurentPlus P b))).trans
    (((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
      (boundedFlatCoefficientBassSquareHomotopy P b)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
      ((boundedFlatCoefficientPolynomialSquareHomotopy P u).symm.postcomp
        (boundedFlatPerfectPrespectrumMap (laurentMinus P b))))

/-- The precise outer left association required by the moving-square conversion. -/
def boundedFlatCoefficientBassPastedTrack :=
  (((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientPlusSquareHomotopy P u)).cast
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    (boundedFlatCoefficientBassTargetTrack P u)).trans
    ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatCoefficientMinusSquareHomotopy P u)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).symm

/-- The initial boundary is the entire original Bass square under coefficient change. -/
theorem boundedFlatCoefficientBassBoundary_source_level (n : ℕ) :
    ((boundedFlatCoefficientBassSquareHomotopy P a).postcomp
      (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))).level
        n =
      ((boundedFlatCoefficientBassBoundary P u).at 0).level n := by
  rw [Homotopy.RelHomotopy.at_zero]
  simp only [boundedFlatCoefficientBassSquareHomotopy, Homotopy.postcomp_trans,
    Homotopy.postcomp_symm]

/-- The constructed boundary ends at the original Bass target cylinder with exact associations. -/
theorem boundedFlatCoefficientBassBoundary_target_level (n : ℕ) :
    (boundedFlatCoefficientBassPastedTrack P u).level n =
      ((boundedFlatCoefficientBassBoundary P u).at 1).level n := by
  rw [Homotopy.RelHomotopy.at_one]
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr
    · rfl
    · apply Homotopy.trans_level_congr
      · rfl
      · apply Homotopy.trans_level_congr
        · unfold boundedFlatCoefficientBassSquareHomotopy
          rw [Homotopy.precomp_trans, Homotopy.precomp_symm]
          apply Homotopy.trans_level_congr
          · apply Homotopy.symm_level_congr
            rfl
          · rfl
        · exact congrArg (fun H ↦ H.level n)
            (Homotopy.postcomp_symm (boundedFlatCoefficientPolynomialSquareHomotopy P u)
              (boundedFlatPerfectPrespectrumMap (laurentMinus P b)))
  · rfl

/-- The original Bass square satisfies the actual coefficient pasted-track relation. -/
def boundedFlatCoefficientBassPasting :
    ((boundedFlatCoefficientBassSquareHomotopy P a).postcomp
      (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map
        u)))).RelHomotopy
      (boundedFlatCoefficientBassPastedTrack P u) :=
  Homotopy.RelHomotopy.ofLevels (boundedFlatCoefficientBassBoundary P u) _ _
    (by intro n; simpa only [Homotopy.RelHomotopy.at_zero] using
      boundedFlatCoefficientBassBoundary_source_level P u n)
    (by intro n; simpa only [Homotopy.RelHomotopy.at_one] using
      boundedFlatCoefficientBassBoundary_target_level P u n)

/-- Regroup the source endpoint maps to the literal span-comparison composition maps. -/
def boundedFlatCoefficientBassSourceDescTrack :=
  ((boundedFlatCoefficientBassSquareHomotopy P a).postcomp
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Regroup the target endpoints to the literal polynomial-coefficient composite maps. -/
def boundedFlatCoefficientBassTargetDescTrack :=
  (boundedFlatCoefficientBassTargetTrack P u).cast (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- The exact boundary now uses the untransported precompositions of both Laurent squares. -/
def boundedFlatCoefficientBassPastedDescTrack :=
  ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientPlusSquareHomotopy P u)).trans
      (boundedFlatCoefficientBassTargetDescTrack P u)).trans
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatCoefficientMinusSquareHomotopy P u)).symm

/-- The genuine geometric boundary filler in the exact moving-pushout descent interface. -/
def boundedFlatCoefficientBassDescPasting :
    (boundedFlatCoefficientBassSourceDescTrack P u).RelHomotopy
      (boundedFlatCoefficientBassPastedDescTrack P u) :=
  Homotopy.RelHomotopy.ofLevels (boundedFlatCoefficientBassPasting P u) _ _ (fun _ ↦ rfl)
    (by
      intro n
      apply Homotopy.trans_level_congr
      · apply Homotopy.trans_level_congr <;> rfl
      · apply Homotopy.symm_level_congr
        rfl)



/-- The target track is the whole original polynomial-span cylinder followed by Bass comparison. -/
theorem boundedFlatCoefficientBassTargetDescTrack_level (n : ℕ) :
    (boundedFlatCoefficientBassTargetDescTrack P u).level n =
      ((HomotopyPushout.mapSquareHomotopy
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))
        (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
        (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
        (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
        (boundedFlatCoefficientPolynomialSquareHomotopy P u)
          (boundedFlatCoefficientPolynomialSquareHomotopy P u)).postcomp
          (boundedFlatCoefficientBassSquareComparison P b)).level n := by
  simp only [boundedFlatCoefficientBassTargetDescTrack, Homotopy.cast_level,
    boundedFlatCoefficientBassTargetTrack, HomotopyPushout.mapSquareHomotopy,
    Homotopy.postcomp_trans]
  apply Homotopy.trans_level_congr
  · rfl
  · apply Homotopy.trans_level_congr <;> rfl

/-- The source descent equals the literal original Bass comparison followed by Laurent change. -/
theorem boundedFlatCoefficientBassSourceDesc_eq :
    HomotopyPushout.desc
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatPerfectPrespectrumMap (laurentPlus P a) ≫
        boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
      (boundedFlatPerfectPrespectrumMap (laurentMinus P a) ≫
        boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
      (boundedFlatCoefficientBassSourceDescTrack P u) =
    boundedFlatCoefficientBassSquareComparison P a ≫
      boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)) := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    rfl

/-- The target descent equals the original polynomial-span map followed by Bass comparison. -/
theorem boundedFlatCoefficientBassTargetDesc_eq :
    HomotopyPushout.desc
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
        boundedFlatPerfectPrespectrumMap (laurentPlus P b))
      (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
        boundedFlatPerfectPrespectrumMap (laurentMinus P b))
      (boundedFlatCoefficientBassTargetDescTrack P u) =
    boundedFlatCoefficientPolynomialSpanMap P u ≫ boundedFlatCoefficientBassSquareComparison P b
      := by
  apply HomotopyPushout.hom_ext
  · rfl
  · rfl
  · intro n s x
    exact DFunLike.congr_fun (boundedFlatCoefficientBassTargetDescTrack_level P u n) (s, x)

/-- The actual geometric moving square descends to the two unchanged coefficient composites. -/
def boundedFlatCoefficientBassComparisonHomotopy :
    Homotopy (boundedFlatCoefficientBassSquareComparison P a ≫
      boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
      (boundedFlatCoefficientPolynomialSpanMap P u ≫ boundedFlatCoefficientBassSquareComparison P
        b) :=
  (HomotopyPushout.descSquareHomotopy
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientPlusSquareHomotopy P u) (boundedFlatCoefficientMinusSquareHomotopy P u)
    (boundedFlatCoefficientBassDescPasting P u).toSquare).cast
      (boundedFlatCoefficientBassSourceDesc_eq P u) (boundedFlatCoefficientBassTargetDesc_eq P u)

/-- The left polynomial endpoint moves through its unchanged positive Laurent square. -/
theorem boundedFlatCoefficientBassComparisonHomotopy_inl (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassComparisonHomotopy P u).level n
      (r, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x) =
      (boundedFlatCoefficientPlusSquareHomotopy P u).level n (r, x) := rfl

/-- The right polynomial endpoint moves through its distinct negative Laurent square. -/
theorem boundedFlatCoefficientBassComparisonHomotopy_inr (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassComparisonHomotopy P u).level n
      (r, (HomotopyPushout.inr
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x) =
      (boundedFlatCoefficientMinusSquareHomotopy P u).level n (r, x) := rfl

/-- The whole actual cylinder retains the square constructed from the proved geometric pasting. -/
theorem boundedFlatCoefficientBassComparisonHomotopy_cylinder (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassComparisonHomotopy P u).level n
      (r, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (s, x)) =
      (boundedFlatCoefficientBassDescPasting P u).toSquare.level n (r, (s, x)) := rfl

/-- The original relative comparison is recovered on every collapsed parameter-square point. -/
theorem boundedFlatCoefficientBassComparisonHomotopy_collapse (n : ℕ)
    (z : unitInterval × unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassComparisonHomotopy P u).level n
      ((Quillen.ThreeSideSquare.collapse z).1, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n
          ((Quillen.ThreeSideSquare.collapse z).2, x)) =
      (boundedFlatCoefficientBassDescPasting P u).level n (z.1, (z.2, x)) :=
  (boundedFlatCoefficientBassDescPasting P u).toSquare_collapse n z x



/-- The genuine comparison-map homotopy induces an actual map of the original Bass square cones. -/
def boundedFlatCoefficientBassConeMap :
    mappingCone (boundedFlatCoefficientBassSquareComparison P a) ⟶
      mappingCone (boundedFlatCoefficientBassSquareComparison P b) :=
  mappingConeSquareMap _ _ (boundedFlatCoefficientPolynomialSpanMap P u)
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedFlatCoefficientBassComparisonHomotopy P u)

/-- Parameter-correct looping gives a map between the actual one-step Bass spectra. -/
def boundedFlatCoefficientBassStepMap : parameterLooping (mappingCone
  (boundedFlatCoefficientBassSquareComparison P a)) ⟶ parameterLooping (mappingCone
  (boundedFlatCoefficientBassSquareComparison P b)) :=
  parameterLoopingMap (boundedFlatCoefficientBassConeMap P u)

/-- The literal Laurent inclusion commutes with the actual coefficient cone map. -/
lemma boundedFlatCoefficientBassConeMap_inclusion :
    mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a) ≫
      boundedFlatCoefficientBassConeMap P u =
      boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)) ≫
        mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b) :=
  mappingConeSquareMap_inclusion _ _ _ _ _

/-- The whole cone cylinder retains the actual coefficient comparison and target cone null track. -/
lemma boundedFlatCoefficientBassConeMap_cylinder (n : ℕ) (s : unitInterval)
    (x : (HomotopyPushout.prespectrum
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).space n) :
    (boundedFlatCoefficientBassConeMap P u).map n
      (ReducedMappingCone.cylinder _ _ ((boundedFlatCoefficientBassSquareComparison P a).map n)
        (s, x)) =
    (((boundedFlatCoefficientBassComparisonHomotopy P u).postcomp
      (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b))).trans
      (Homotopy.precomp (boundedFlatCoefficientPolynomialSpanMap P u)
        (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P b)))).level n (s, x) :=
          rfl


/-- The unchanged positive source leg maps to its literal polynomial endpoint. -/
theorem boundedFlatCoefficientBassSourceLeg_span :
    boundedFlatCoefficientBassSourceLeg P a ≫ boundedFlatCoefficientPolynomialSpanMap P u =
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P a) ≫
        boundedFlatPerfectPrespectrumMap
          (coefficientMap P ((polynomialUnderFunctor R).map u))) ≫
          HomotopyPushout.inl
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))
            (boundedFlatPerfectPrespectrumMap (polynomialProjection P b)) := by
  unfold boundedFlatCoefficientBassSourceLeg
  rw [Category.assoc, inl_boundedFlatCoefficientPolynomialSpanMap, Category.assoc]

/-- The original geometric polynomial square moves the unchanged positive source leg. -/
def boundedFlatCoefficientBassSourceLegHomotopy :
    Homotopy
      (boundedFlatCoefficientBassSourceLeg P a ≫ boundedFlatCoefficientPolynomialSpanMap P u)
      (boundedFlatPerfectPrespectrumMap (coefficientMap P u) ≫
        boundedFlatCoefficientBassSourceLeg P b) :=
  ((boundedFlatCoefficientPolynomialSquareHomotopy P u).postcomp
    (HomotopyPushout.inl
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P b)))).cast
      (boundedFlatCoefficientBassSourceLeg_span P u).symm (Category.assoc _ _ _)

/-- Source movement and the original raw cone contraction keep their parameters independent. -/
def boundedFlatCoefficientBassSourceLegConeSquare :=
  Homotopy.Square.interchange (boundedFlatCoefficientBassSourceLegHomotopy P u)
    (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P b))

theorem boundedFlatCoefficientBassSourceLegConeSquare_apply (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientBassSourceLegConeSquare P u).level n (r, (s, x)) =
      (mappingConeHomotopy (boundedFlatCoefficientBassSquareComparison P b)).level n
        (s, (boundedFlatCoefficientBassSourceLegHomotopy P u).level n (r, x)) := rfl

/-- The positive source-leg movement retains its complete original cone boundary. -/
def boundedFlatCoefficientBassSourceLegConeBoundary :=
  (boundedFlatCoefficientBassSourceLegConeSquare P u).toBoundary

/-- Parameter looping applies the same raw cone map at each independent loop coordinate. -/
theorem boundedFlatCoefficientBassStepMap_apply (n : ℕ) (s : unitInterval)
    (x : (parameterLooping
      (mappingCone (boundedFlatCoefficientBassSquareComparison P a))).space n) :
    Path.toContinuousMap ((boundedFlatCoefficientBassStepMap P u).map n x) s =
      (boundedFlatCoefficientBassConeMap P u).map n (Path.toContinuousMap x s) := rfl

end Quillen.PerfectComplexes
