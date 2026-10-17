/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftConeSquares
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftPolynomialNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveSupportMap
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveReanchorFamily
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenEvaluation

/-!
# Native values of the finite left-route cone squares

The statements use every original native level and every input, including genuine loops
in degree zero. Evaluation is separate from the full-reference carrier seams. The first
square evaluates to the original cone_q map on the p polynomial cylinder, with its exact
two halves; no globally continuous evaluator or carrier-level cone_q map is introduced.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftConeSquareNative
open BassH0Merge CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveC0CarrierSeed CoefficientBassPositiveLeftCellParameters
open CoefficientBassPositiveLeftPolynomialParameters CoefficientBassPositiveLeftPolynomialNative
open CoefficientBassPositiveLeftConeSquares
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

private theorem product_family_native (n : ℕ) (t s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumFamily (laurentReference P p q)
      (BassH1References.chartNodes P p q (underToLaurent R) (laurentPlus_projection P b)) n
      (Quillen.SimplexGrid.parameter.{u + 1} 4 4
        (NativeSquareFiveSimplex.parameter t, NativeSquareFiveSimplex.parameter s), x) =
      (boundedFlatCoefficientPlusSquareHomotopy P q).level n
        (s, (boundedFlatCoefficientPolynomialSquareHomotopy P p).level n (t, x)) := by
  rw [prespectrumFamily_eq, BassH1References.chart_original]
  exact BassH1Components.plus_native P p q n s t x

/-- Both actual common-reference versions of Z evaluate to the same composed native squares. -/
theorem Z_native (e : Bool) (n : ℕ) (t s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    pointwisePrespectrumFamily (laurentReference P p q) n (Z P p q e (t, s)) x =
      (boundedFlatCoefficientPlusSquareHomotopy P q).level n
        (s, (boundedFlatCoefficientPolynomialSquareHomotopy P p).level n (t, x)) := by
  change pointwisePrespectrumFamily _ n (parameter _ _ _) x = _
  rw [pointwisePrespectrumFamily_parameter]
  cases e
  · exact product_family_native P p q n t s x
  · change prespectrumFamily (laurentReference P p q)
      (ModelSimplex.reanchorNodes (LaurentUnitReferenceSpecialization.commonUnit P p q)
        (BassH1References.chartNodes P p q (underToLaurent R) (laurentPlus_projection P b))) n
      (_, x) = _
    rw [prespectrumFamily_reanchor]
    exact product_family_native P p q n t s x

/-- The two separately attached cylinders retain their coordinate and full native input. -/
theorem cylinder_native (e : Bool) (n : ℕ)
    (y : |nerve (Codiscrete (Node (polynomialReference P p q)))|) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n (cylinder P p q e (y, s)) x =
      ReducedMappingCone.cylinder _ _
        ((boundedFlatPerfectPrespectrumMap (laurentPlus P c)).map n)
        (s, pointwisePrespectrumFamily (polynomialReference P p q) n y x) := by
  cases e
  · exact CutOpenCarrier.nativeEval_cylinderMinus _ _ _ _ _ n y s x
  · exact CutOpenCarrier.nativeEval_cylinderPlus _ _ _ _ _ n y s x

/-- The original first half of cone_q, at exactly s/2, with independent polynomial time t. -/
theorem A_lower_native (e : Bool) (n : ℕ) (t s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n
        (A P p q e (t, Quillen.NativePathCells.lower s)) x =
      (mappingConeInclusion (boundedFlatPerfectPrespectrumMap (laurentPlus P c))).map n
        ((boundedFlatCoefficientPlusSquareHomotopy P q).level n
          (s, (boundedFlatCoefficientPolynomialSquareHomotopy P p).level n (t, x))) := by
  rw [A_lower, CutOpenCarrier.nativeEval_laurentInclusion, Z_native]; rfl

/-- The original second half of cone_q, at exactly (s+1)/2, is the target polynomial cylinder. -/
theorem A_upper_native (e : Bool) (n : ℕ) (t s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n
        (A P p q e (t, Quillen.NativePathCells.upper s)) x =
      ReducedMappingCone.cylinder _ _
        ((boundedFlatPerfectPrespectrumMap (laurentPlus P c)).map n)
        (s, (boundedFlatPerfectPrespectrumMap
          (coefficientMap P ((polynomialUnderFunctor R).map q))).map n
          ((boundedFlatCoefficientPolynomialSquareHomotopy P p).level n (t, x))) := by
  rw [A_upper, cylinder_native, first_parameter_native]

/-- The entire A± square is the unchanged original cone_q on the p polynomial cylinder. -/
theorem A_native (e : Bool) (n : ℕ) (t s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n (A P p q e (t, s)) x =
      (boundedFlatCoefficientBassPositiveConeMap P q).map n
        (ReducedMappingCone.cylinder _ _
          ((boundedFlatPerfectPrespectrumMap (laurentPlus P b)).map n)
          (s, (boundedFlatCoefficientPolynomialSquareHomotopy P p).level n (t, x))) := by
  rcases Quillen.NativePathCells.cover s with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · rw [A_lower_native]
    exact (mappingConeSquareMap_first_half
      (boundedFlatPerfectPrespectrumMap (laurentPlus P b))
      (boundedFlatPerfectPrespectrumMap (laurentPlus P c))
      (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map q)))
      (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map q)))
      (boundedFlatCoefficientPlusSquareHomotopy P q) n r
      ((boundedFlatCoefficientPolynomialSquareHomotopy P p).level n (t, x))).symm
  · rw [A_upper_native]
    exact (mappingConeSquareMap_second_half
      (boundedFlatPerfectPrespectrumMap (laurentPlus P b))
      (boundedFlatPerfectPrespectrumMap (laurentPlus P c))
      (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map q)))
      (boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map q)))
      (boundedFlatCoefficientPlusSquareHomotopy P q) n r
      ((boundedFlatCoefficientPolynomialSquareHomotopy P p).level n (t, x))).symm

/-- Equivalent source statement using the original ConeMapNull, without choosing a new null. -/
theorem A_native_null (e : Bool) (n : ℕ) (t s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n (A P p q e (t, s)) x =
      (boundedFlatCoefficientBassPositiveConeMapNull P q).level n
        (s, (boundedFlatCoefficientPolynomialSquareHomotopy P p).level n (t, x)) :=
  (A_native P p q e n t s x).trans
    (boundedFlatCoefficientBassPositiveConeMap_cylinder P q n s
      ((boundedFlatCoefficientPolynomialSquareHomotopy P p).level n (t, x)))

/-- The entire B± square is the original q polynomial movement precomposed by coefficient p. -/
theorem B_native (e : Bool) (n : ℕ) (t s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n (B P p q e (t, s)) x =
      ReducedMappingCone.cylinder _ _
        ((boundedFlatPerfectPrespectrumMap (laurentPlus P c)).map n)
        (s, (boundedFlatCoefficientPolynomialSquareHomotopy P q).level n
          (t, (boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) := by
  change CutOpenCarrier.nativeEval _ _ _ _ _ n
    (cylinder P p q e (secondParameter P p q t, s)) x = _
  rw [cylinder_native, second_parameter_native]

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftConeSquareNative
