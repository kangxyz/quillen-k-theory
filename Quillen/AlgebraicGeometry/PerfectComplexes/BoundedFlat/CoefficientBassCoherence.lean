/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Naturality
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassMap
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SquareTrackOriginal
public import Quillen.Topology.Prespectrum.ParameterLoopingHomotopy
public import Quillen.Topology.Prespectrum.PushoutHomotopy
public import Quillen.Topology.Prespectrum.ConeHomotopy
public import Quillen.Topology.Prespectrum.HomotopySquareComposition

/-!
# Original raw coefficient identity and composition faces

This module retains the actual original coefficient pullback maps and their
canonical identity and binary composition tracks. It supplies coherence faces of the fixed raw
Bass maps for an arbitrary ambient scheme, without flatness or compactness assumptions.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The fixed coefficient fiber retains its original geometric identity. -/
theorem boundedFlatCoefficientGeometricIdentity (a : Under R) :
    coefficientMap P (𝟙 a) = 𝟙 (space (op P, a)) := by
  change AlgebraicGeometry.Scheme.BaseChange.Coefficients.map (𝟙 (op P, a)) = _
  exact AlgebraicGeometry.Scheme.BaseChange.Coefficients.map_id (op P, a)

/-- The original coefficient identity map has its actual geometric and normalization track. -/
def boundedFlatCoefficientIdentityHomotopy (a : Under R) :
    Homotopy (boundedFlatPerfectPrespectrumMap (coefficientMap P (𝟙 a)))
      (𝟙 (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a))))) :=
  (boundedFlatPerfectPrespectrumIdHomotopy (space (op P, a))).cast
    (congrArg boundedFlatPerfectPrespectrumMap
      (boundedFlatCoefficientGeometricIdentity P a)).symm rfl

/-- The actual original coefficient composition retains contravariant scheme order. -/
def boundedFlatCoefficientCompositionHomotopy {a b c : Under R}
    (u : a ⟶ b) (v : b ⟶ c) :
    Homotopy (boundedFlatPerfectPrespectrumMap (coefficientMap P (u ≫ v)))
      (boundedFlatPerfectPrespectrumMap (coefficientMap P u) ≫
        boundedFlatPerfectPrespectrumMap (coefficientMap P v)) :=
  (boundedFlatPerfectPrespectrumCompHomotopy (coefficientMap P v)
    (coefficientMap P u)).cast
    (congrArg boundedFlatPerfectPrespectrumMap (coefficientMap_comp P u v)).symm rfl

variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The polynomial endpoint composition track on the unchanged native polynomial fibers. -/
def boundedFlatCoefficientPolynomialCompositionHomotopy :
    Homotopy
      (boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v))))
      (boundedFlatPerfectPrespectrumMap
          (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
        boundedFlatPerfectPrespectrumMap
          (coefficientMap P ((polynomialUnderFunctor R).map v))) :=
  (boundedFlatCoefficientCompositionHomotopy P
    ((polynomialUnderFunctor R).map u) ((polynomialUnderFunctor R).map v)).cast
      (congrArg (fun k ↦ boundedFlatPerfectPrespectrumMap (coefficientMap P k))
        ((polynomialUnderFunctor R).map_comp u v)).symm rfl

/-- The original Laurent coefficient composition track, on the actual raw cone target. -/
def boundedFlatCoefficientLaurentCompositionHomotopy :
    Homotopy
      (boundedFlatPerfectPrespectrumMap
        (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v))))
      (boundedFlatPerfectPrespectrumMap
          (coefficientMap P ((laurentUnderFunctor R).map u)) ≫
        boundedFlatPerfectPrespectrumMap
          (coefficientMap P ((laurentUnderFunctor R).map v))) :=
  (boundedFlatCoefficientCompositionHomotopy P
    ((laurentUnderFunctor R).map u) ((laurentUnderFunctor R).map v)).cast
      (congrArg (fun k ↦ boundedFlatPerfectPrespectrumMap (coefficientMap P k))
        ((laurentUnderFunctor R).map_comp u v)).symm rfl

/-- The fixed polynomial coefficient square, with explicit native geometric endpoints. -/
theorem boundedFlatCoefficientPolynomialGeometricNaturality {a b : Under R} (u : a ⟶ b) :
    coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a =
      polynomialProjection P b ≫ coefficientMap P u :=
  AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
    (polynomialUnderCoefficient R) u

/-- The existing rectangle comparison is used in the coefficient-composition direction. -/
def boundedFlatCoefficientPolynomialTransposedRectangle :=
  DoubleSquareTrack.originalComparison
    (coefficientMap P u) (coefficientMap P v)
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
    (boundedFlatCoefficientPolynomialGeometricNaturality P u).symm
    (boundedFlatCoefficientPolynomialGeometricNaturality P v).symm

/-- The two successive original polynomial squares, with literal association casts. -/
def boundedFlatCoefficientPolynomialCompositeSquare :
    Homotopy
      ((boundedFlatPerfectPrespectrumMap (polynomialProjection P a) ≫
        boundedFlatPerfectPrespectrumMap
          (coefficientMap P ((polynomialUnderFunctor R).map u))) ≫
        boundedFlatPerfectPrespectrumMap
          (coefficientMap P ((polynomialUnderFunctor R).map v)))
      ((boundedFlatPerfectPrespectrumMap (coefficientMap P u) ≫
        boundedFlatPerfectPrespectrumMap (coefficientMap P v)) ≫
        boundedFlatPerfectPrespectrumMap (polynomialProjection P c)) :=
  ((boundedFlatCoefficientPolynomialSquareHomotopy P u).postcomp
    (boundedFlatPerfectPrespectrumMap
      (coefficientMap P ((polynomialUnderFunctor R).map v)))).trans
      ((Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
        (boundedFlatCoefficientPolynomialSquareHomotopy P v)).cast
        (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm)

/-- Original source-fiber composition followed by the unchanged target projection. -/
def boundedFlatCoefficientPolynomialSourceCompositionTrack :=
  (boundedFlatCoefficientCompositionHomotopy P u v).postcomp
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))

/-- Original polynomial composition, precomposed by the unchanged source projection. -/
def boundedFlatCoefficientPolynomialTargetCompositionTrack :=
  (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientPolynomialCompositionHomotopy P u v)).cast rfl
    (Category.assoc _ _ _).symm

/-- Reversing the geometric square swaps its two original composition routes. -/
theorem boundedFlatGeometricSquareReverse_level {X Y Z T : Scheme.{u}}
    (p : X ⟶ Y) (v : Y ⟶ Z) (q : X ⟶ T) (w : T ⟶ Z)
    (h : p ≫ v = q ≫ w) (n : ℕ) :
    (boundedFlatPerfectPrespectrumSquareHomotopy q w p v h.symm).symm.level n =
      (boundedFlatPerfectPrespectrumSquareHomotopy p v q w h).level n := by
  have first := Homotopy.symm_level_congr _ _ n
    (boundedFlatPerfectPrespectrumSquareHomotopy_level q w p v h.symm n)
  have middle := Homotopy.reverseTwoRoutes_level
    (boundedFlatPerfectPrespectrumCompHomotopy p v)
    (boundedFlatPerfectPrespectrumCompHomotopy q w)
    (congrArg boundedFlatPerfectPrespectrumMap h) n
  exact first.trans (middle.trans
    (boundedFlatPerfectPrespectrumSquareHomotopy_level p v q w h n).symm)

/-- Equal geometric arrows identify full original square levels, independently of proof
    transport. -/
theorem boundedFlatGeometricSquare_level_congr {X Y Z T : Scheme.{u}}
    {p p' : X ⟶ Y} {v v' : Y ⟶ Z} {q q' : X ⟶ T} {w w' : T ⟶ Z}
    (h : p ≫ v = q ≫ w) (h' : p' ≫ v' = q' ≫ w')
    (hp : p = p') (hv : v = v') (hq : q = q') (hw : w = w') (n : ℕ) :
    (boundedFlatPerfectPrespectrumSquareHomotopy p v q w h).level n =
      (boundedFlatPerfectPrespectrumSquareHomotopy p' v' q' w' h').level n := by
  subst p' v' q' w'
  rfl

/-- The transposed rectangle retains precisely the reversed two original polynomial squares. -/
theorem boundedFlatCoefficientPolynomialTransposedRectangle_source_level (n : ℕ) :
    (boundedFlatCoefficientPolynomialCompositeSquare P u v).level n =
      (((boundedFlatCoefficientPolynomialTransposedRectangle P u v).symmPath).at 0).level n := by
  rw [Homotopy.RelHomotopy.at_zero]
  unfold DoubleSquareTrack.originalLeft
  rw [Homotopy.symm_trans]
  unfold boundedFlatCoefficientPolynomialCompositeSquare
  apply Homotopy.trans_level_congr
  · rw [← Homotopy.postcomp_symm]
    apply Homotopy.postcomp_level_congr
    exact (boundedFlatGeometricSquareReverse_level
      (coefficientMap P ((polynomialUnderFunctor R).map u))
      (polynomialProjection P a) (polynomialProjection P b) (coefficientMap P u)
      (boundedFlatCoefficientPolynomialGeometricNaturality P u) n).symm
  · change (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
      (boundedFlatCoefficientPolynomialSquareHomotopy P v)).level n =
        (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
          (boundedFlatPerfectPrespectrumSquareHomotopy (polynomialProjection P c)
            (coefficientMap P v) (coefficientMap P ((polynomialUnderFunctor R).map v))
            (polynomialProjection P b)
            (boundedFlatCoefficientPolynomialGeometricNaturality P v).symm)).symm.level n
    rw [← Homotopy.precomp_symm]
    apply Homotopy.precomp_level_congr
    exact (boundedFlatGeometricSquareReverse_level
      (coefficientMap P ((polynomialUnderFunctor R).map v))
      (polynomialProjection P b) (polynomialProjection P c) (coefficientMap P v)
      (boundedFlatCoefficientPolynomialGeometricNaturality P v) n).symm

/-- The transposed target uses both unchanged original coefficient composition tracks. -/
theorem boundedFlatCoefficientPolynomialTransposedRectangle_target_level (n : ℕ) :
    (((boundedFlatCoefficientPolynomialTargetCompositionTrack P u v).symm.trans
      (boundedFlatCoefficientPolynomialSquareHomotopy P (u ≫ v))).trans
      (boundedFlatCoefficientPolynomialSourceCompositionTrack P u v)).level n =
      (((boundedFlatCoefficientPolynomialTransposedRectangle P u v).symmPath).at 1).level n := by
  rw [Homotopy.RelHomotopy.at_one]
  unfold DoubleSquareTrack.originalRight
  rw [Homotopy.symm_trans, Homotopy.symm_trans, Homotopy.symm_symm]
  apply Homotopy.trans_level_congr
  · apply Homotopy.trans_level_congr
    · apply Homotopy.symm_level_congr
      rfl
    · refine (boundedFlatGeometricSquareReverse_level
        (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
        (polynomialProjection P a) (polynomialProjection P c) (coefficientMap P (u ≫ v))
        (boundedFlatCoefficientPolynomialGeometricNaturality P (u ≫ v)) n).symm.trans ?_
      apply Homotopy.symm_level_congr
      exact boundedFlatGeometricSquare_level_congr _ _ rfl (coefficientMap_comp P u v)
        ((congrArg (coefficientMap P) ((polynomialUnderFunctor R).map_comp u v)).trans
          (coefficientMap_comp P ((polynomialUnderFunctor R).map u)
            ((polynomialUnderFunctor R).map v))) rfl n
  · rfl

/-- Whole original polynomial square composition, supplied by the maintained rectangle owner. -/
def boundedFlatCoefficientPolynomialSquareCompositionComparison :
    (boundedFlatCoefficientPolynomialCompositeSquare P u v).RelHomotopy
      (((boundedFlatCoefficientPolynomialTargetCompositionTrack P u v).symm.trans
        (boundedFlatCoefficientPolynomialSquareHomotopy P (u ≫ v))).trans
        (boundedFlatCoefficientPolynomialSourceCompositionTrack P u v)) :=
  Homotopy.RelHomotopy.ofLevels
    (boundedFlatCoefficientPolynomialTransposedRectangle P u v).symmPath _ _
    (by intro n; simpa only [Homotopy.RelHomotopy.at_zero] using
      boundedFlatCoefficientPolynomialTransposedRectangle_source_level P u v n)
    (by intro n; simpa only [Homotopy.RelHomotopy.at_one] using
      boundedFlatCoefficientPolynomialTransposedRectangle_target_level P u v n)

end Quillen.PerfectComplexes
