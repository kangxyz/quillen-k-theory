/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftPairedNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftConeSquareNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveLeftNativePostcomp
public import Quillen.Topology.Path.CarrierSquareBoundaryEvaluation
public import Quillen.Topology.Prespectrum.RelativeHomotopyTerminalEvaluation

/-! Both actual left cone comparisons retain the original collapse and terminal-pause clocks. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveLeftConeComparisonNative
open CommonReferenceNerve CoefficientBassPositiveC1BoundaryLift
open CoefficientBassPositiveLeftConeSquares CoefficientBassPositiveLeftPairedNull
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The original interchange for an arbitrary coefficient arrow, at a genuine native input. -/
def nativeSquare (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CarrierPathSquare.Square ((CoefficientBassPositiveNullTrack.oldCone P p).path n x)
      ((CoefficientBassPositiveNullTrack.newCone P p).path n x)
      ((CoefficientBassPositiveNullTrack.polynomialMovement P p).path n x)
      (Path.refl ((mappingCone (boundedFlatPerfectPrespectrumMap (laurentPlus P b))).point n)) := by
  let J := Homotopy.Square.interchange (boundedFlatCoefficientPolynomialSquareHomotopy P p)
    (mappingConeHomotopy (boundedFlatPerfectPrespectrumMap (laurentPlus P b)))
  exact {
    parameter := ⟨fun z ↦ J.level n (z.1, (z.2, x)), by fun_prop⟩
    at_zero := fun s ↦ J.at_zero n s x
    at_one := fun s ↦ J.at_one n s x
    left := fun r ↦ J.left n r x
    right := fun r ↦ J.right n r x }

private theorem relativeTrans_level_apply {E F : LoopPrespectrum.{u}}
    {f g : E ⟶ F} {H K L : Homotopy f g}
    (J : H.RelHomotopy K) (J' : K.RelHomotopy L)
    (n : ℕ) (r s : I) (x : E.space n) :
    (J.trans J').level n (r, (s, x)) =
      ((J.level n).trans (J'.level n)) (r, (s, x)) := rfl

/-- The full original conePasting, including ofLevels and the second-half transRefl. -/
theorem nativeSquare_conePasting (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (nativeSquare P p n x).coneBoundary (r, s) =
      (CoefficientBassPositiveNullTrack.conePasting P p).level n (r, (s, x)) := by
  rw [CarrierPathSquare.Square.coneBoundary_apply]
  unfold CoefficientBassPositiveNullTrack.conePasting
  rw [relativeTrans_level_apply, ContinuousMap.HomotopyRel.trans_apply]
  split_ifs
  · rw [Homotopy.RelHomotopy.ofLevels_apply, Homotopy.Square.toBoundary_apply]
    rfl
  · rw [Homotopy.RelHomotopy.transRefl_apply_path, Homotopy.path_trans]

/-- Continuous cone postcomposition maps all four native edges and both square coordinates. -/
abbrev mappedSquare (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :=
  (nativeSquare P p n x).map ((boundedFlatCoefficientBassPositiveConeMap P q).map n)

/-- The first whole comparison evaluates to the original p conePasting postcomposed by cone_q. -/
theorem first_cone_native (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n
      (firstConeComparison P p q e (r, s)) x =
      (boundedFlatCoefficientBassPositiveConeMap P q).map n
        ((CoefficientBassPositiveNullTrack.conePasting P p).level n (r, (s, x))) := by
  rw [first_cone_comparison_apply]
  have h := (ASquare P p q e).coneBoundary_natural (mappedSquare P p q n x)
    (fun y ↦ CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n y x)
    (fun t v ↦ CoefficientBassPositiveLeftConeSquareNative.A_native P p q e n t v x) r s
  have hm := (nativeSquare P p n x).coneBoundary_natural (mappedSquare P p q n x)
    ((boundedFlatCoefficientBassPositiveConeMap P q).map n) (fun _ _ ↦ rfl) r s
  exact h.trans (hm.symm.trans
    (congrArg ((boundedFlatCoefficientBassPositiveConeMap P q).map n)
      (nativeSquare_conePasting P p n r s x)))

/-- The middle whole comparison uses the original q conePasting on coefficient_p(x). -/
theorem middle_cone_native (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n
      (middleConeComparison P p q e (r, s)) x =
      (CoefficientBassPositiveNullTrack.conePasting P q).level n
        (r, (s, (boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) := by
  rw [middle_cone_comparison_apply]
  exact ((BSquare P p q e).coneBoundary_natural
    (nativeSquare P q n ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))
    (fun y ↦ CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n y x)
    (fun t v ↦ CoefficientBassPositiveLeftConeSquareNative.B_native P p q e n t v x) r s).trans
      (nativeSquare_conePasting P q n r s
        ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x))

/-- The first comparison also matches the explicitly typed postcomposed native wrapper. -/
theorem first_cone_native_wrapper (e : Bool) (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n
      (firstConeComparison P p q e (r, s)) x =
      (CoefficientBassPositiveLeftNativePostcomp.conePasting P p q).level n (r, (s, x)) :=
  (first_cone_native P p q e n r s x).trans
    (CoefficientBassPositiveLeftNativePostcomp.conePasting_mapped P p q n x r s)

/-- The full first old cone rail retains its original native path clock. -/
theorem first_oldCone_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n
      (firstOldCone P p q e s) x =
      (CoefficientBassPositiveLeftNativePostcomp.oldCone P p q).level n (s, x) := by
  have h : CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n
      (A P p q e (0, s)) x =
        (boundedFlatCoefficientBassPositiveConeMap P q).map n
          ((nativeSquare P p n x).parameter (0, s)) :=
    CoefficientBassPositiveLeftConeSquareNative.A_native P p q e n 0 s x
  rw [(nativeSquare P p n x).at_zero] at h
  rw [A_path] at h
  exact h

/-- The full first new cone rail retains its original native path clock. -/
theorem first_newCone_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n
      (firstNewCone P p q e s) x =
      (CoefficientBassPositiveLeftNativePostcomp.newCone P p q).level n (s, x) := by
  have h : CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n
      (A P p q e (1, s)) x =
        (boundedFlatCoefficientBassPositiveConeMap P q).map n
          ((nativeSquare P p n x).parameter (1, s)) :=
    CoefficientBassPositiveLeftConeSquareNative.A_native P p q e n 1 s x
  rw [(nativeSquare P p n x).at_one] at h
  rw [A_path] at h
  exact h

/-- The full middle old cone rail retains its original native path clock. -/
theorem middle_oldCone_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n
      (middleOldCone P p q e s) x =
      (CoefficientBassPositiveNullTrack.oldCone P q).level n
        (s, ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) := by
  have h : CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n
      (B P p q e (0, s)) x =
        (nativeSquare P q n
          ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)).parameter (0, s) :=
    CoefficientBassPositiveLeftConeSquareNative.B_native P p q e n 0 s x
  rw [(nativeSquare P q n
    ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)).at_zero] at h
  exact h

/-- The full middle new cone rail retains its original native path clock. -/
theorem middle_newCone_native (e : Bool) (n : ℕ) (s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n
      (middleNewCone P p q e s) x =
      (CoefficientBassPositiveNullTrack.newCone P q).level n
        (s, ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)) := by
  have h : CutOpenCarrier.nativeEval (polynomialReference P p q) (chartMap P (c := c))
      (laurentReference P p q) (ordinaryAnchor P p q)
      (LaurentUnitReferenceSpecialization.shiftedAnchor P p q) n
      (B P p q e (1, s)) x =
        (nativeSquare P q n
          ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)).parameter (1, s) :=
    CoefficientBassPositiveLeftConeSquareNative.B_native P p q e n 1 s x
  rw [(nativeSquare P q n
    ((boundedFlatPerfectPrespectrumMap (coefficientMap P p)).map n x)).at_one] at h
  exact h

end Quillen.PerfectComplexes.CoefficientBassPositiveLeftConeComparisonNative
