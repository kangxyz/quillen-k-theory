/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveSupportMap
public import Quillen.Topology.Prespectrum.HomotopySquareMappedSupport

/-!
# Exact paused positive-cone composition

The polynomial-side track retains the terminal constant half of the fixed original span
composition. The actual paused plus chart and the entire original moving-null construction
give composition of the positive cone maps. Its strict-inclusion image is compared with the
fixed whole-cone C1 restriction; no mixed J0 compatibility or higher filler is assumed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveCompositionTrack
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The original polynomial composition keeps the fixed span track's terminal constant half. -/
def polynomialComposition :=
  (boundedFlatCoefficientPolynomialCompositionHomotopy P u v).trans
    (Quillen.LoopPrespectrum.Homotopy.refl
      (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
        boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map v))))

/-- The exact paused polynomial track is the original span composition on its positive face. -/
theorem polynomialComposition_inl (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (HomotopyPushout.inl
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))).map n
        ((polynomialComposition P u v).level n (r, x)) =
    (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v).level n
      (r, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x) := by
  rw [boundedFlatCoefficientPolynomialSpanCompositionHomotopy_inl]
  change ((polynomialComposition P u v).postcomp
    (HomotopyPushout.inl
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P c)))).level n (r, x) = _
  unfold polynomialComposition
  rw [Homotopy.postcomp_trans]
  rfl

/-- The fixed original paused plus chart, with only its boundary levels identified. -/
def comparisonSquare :
    (boundedFlatCoefficientPlusSquareHomotopy P (u ≫ v)).Square
      (coneSquarePastedHomotopy
        (boundedFlatPerfectPrespectrumMap (laurentPlus P a))
        (boundedFlatPerfectPrespectrumMap (laurentPlus P b))
        (boundedFlatPerfectPrespectrumMap (laurentPlus P c))
        (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
        (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
        (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map v)))
        (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map v)))
        (boundedFlatCoefficientPlusSquareHomotopy P u)
        (boundedFlatCoefficientPlusSquareHomotopy P v))
      (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (laurentPlus P a))
        (boundedFlatCoefficientLaurentCompositionHomotopy P u v))
      ((polynomialComposition P u v).postcomp
        (boundedFlatPerfectPrespectrumMap (laurentPlus P c))) := by
  refine (boundedFlatCoefficientBassCompositionPlusChart P u v).ofBoundaryLevels
    _ _ _ _ ?_ ?_ ?_ ?_
  · intro n
    rfl
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    change (((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) (r, x)) =
      (((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n))
        (r, (HomotopyPushout.inl
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x))
    rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
    split <;> rfl
  · intro n
    rfl
  · intro n
    apply ContinuousMap.ext
    rintro ⟨r, x⟩
    exact congrArg ((boundedFlatCoefficientBassSquareComparison P c).map n)
      (polynomialComposition_inl P u v n r x)

/-- The positive chart keeps every coordinate of the original fixed whole comparison on inl. -/
theorem comparisonSquare_inl (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (comparisonSquare P u v).level n (r, (s, x)) =
    (BassMWhole.comparisonSquare P u v).level n
      (r, (s, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x)) :=
  (BassMWhole.comparison_inl P u v n r s x).symm

/-- The full original moving-null square, with the mandatory paused polynomial boundary. -/
def nullSquare :=
  coneSquareCompositionMovingNullSquare
    (boundedFlatPerfectPrespectrumMap (laurentPlus P a))
    (boundedFlatPerfectPrespectrumMap (laurentPlus P b))
    (boundedFlatPerfectPrespectrumMap (laurentPlus P c))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map v)))
    (boundedFlatCoefficientPlusSquareHomotopy P u)
    (boundedFlatCoefficientPlusSquareHomotopy P v)
    (boundedFlatCoefficientPlusSquareHomotopy P (u ≫ v))
    (polynomialComposition P u v) (boundedFlatCoefficientLaurentCompositionHomotopy P u v)
    (comparisonSquare P u v)

/-- Composition of the actual positive cone maps, through the fixed paused chart recipe. -/
def coneComposition :
    Homotopy (boundedFlatCoefficientBassPositiveConeMap P (u ≫ v))
      (boundedFlatCoefficientBassPositiveConeMap P u ≫
        boundedFlatCoefficientBassPositiveConeMap P v) :=
  coneSquareCompositionHomotopyOfSquare
    (boundedFlatPerfectPrespectrumMap (laurentPlus P a))
    (boundedFlatPerfectPrespectrumMap (laurentPlus P b))
    (boundedFlatPerfectPrespectrumMap (laurentPlus P c))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map v)))
    (boundedFlatCoefficientPlusSquareHomotopy P u)
    (boundedFlatCoefficientPlusSquareHomotopy P v)
    (boundedFlatCoefficientPlusSquareHomotopy P (u ≫ v))
    (polynomialComposition P u v) (boundedFlatCoefficientLaurentCompositionHomotopy P u v)
    (comparisonSquare P u v)

/-- The actual positive cone cylinder retains the whole two-parameter moving-null square. -/
theorem coneComposition_cylinder (n : ℕ) (r s : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (coneComposition P u v).level n
      (r, ReducedMappingCone.cylinder _ _
        ((boundedFlatPerfectPrespectrumMap (laurentPlus P a)).map n) (s, x)) =
    (nullSquare P u v).level n (r, (s, x)) := rfl

end Quillen.PerfectComplexes.CoefficientBassPositiveCompositionTrack
