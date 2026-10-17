/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientLaurentUnitTenNodes
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCompactFamily

/-!
# The chosen Laurent unit pasting on its actual ten-reference family

The fixed scalar surface repeats the original intertwining recipe, including its five outer
pieces and the existing eight-piece rotation. Lower and unit-shifted composition routes remain
distinct carrier paths. The whole actual relative homotopy factors through the common-reference
nerve; no higher filler, comparison, or compatibility certificate is supplied.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientLaurentUnitPastingLift
open CoefficientLaurentUnitTenNodes

/-- The literal intertwining parameter retains separate lower and unit-shifted routes. -/
def parameter :
    (V.trans (C1.symm.trans D1)).Homotopy ((C0.symm.trans D0).trans W) :=
  (Path.Homotopy.transAssoc V C1.symm D1).symm.trans
    ((((Quillen.SimplexParameters.rotate oldParameter).symm).hcomp
        (Path.Homotopy.refl D1)).trans
      ((Path.Homotopy.transAssoc C0.symm U D1).trans
        (((Path.Homotopy.refl C0.symm).hcomp newParameter.symm).trans
          (Path.Homotopy.transAssoc C0.symm D0 W).symm)))

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (u : a ⟶ b)

/-- Every point recovers the chosen native five-piece intertwining, without replacing its recipe. -/
theorem native_lift : HomotopyLift (simplex P u) parameter
    (CoefficientLaurentUnitTrack.squarePasting P u) := by
  let S := simplex P u
  have hc0 := C0_native P u
  have hc1 := C1_native P u
  have hd0 := D0_native P u
  have hd1 := D1_native P u
  have hjc := old_comparison_lift P u
  have hjd := new_comparison_lift P u
  have hu := PathLift.trans_left S (HomotopyLift.target S hjc)
  have hv := PathLift.trans_right S (HomotopyLift.source S hjc)
  have hw := PathLift.trans_right S (HomotopyLift.source S hjd)
  have hrot := HomotopyLift.rotate S hc0 hv hu hc1 hjc
  have h1 := HomotopyLift.symm S
    (PathLift.transAssoc S hv (PathLift.symm S hc1) hd1)
  have h2 := HomotopyLift.hcomp S (HomotopyLift.symm S hrot)
    (PathLift.refl S hd1)
  have h3 := PathLift.transAssoc S (PathLift.symm S hc0) hu hd1
  have h4 := HomotopyLift.hcomp S
    (PathLift.refl S (PathLift.symm S hc0)) (HomotopyLift.symm S hjd)
  have h5 := HomotopyLift.symm S
    (PathLift.transAssoc S (PathLift.symm S hc0) hd0 hw)
  exact HomotopyLift.trans S h1 (HomotopyLift.trans S h2
    (HomotopyLift.trans S h3 (HomotopyLift.trans S h4 h5)))

/-- The original Laurent-square endpoint transport changes no point of the scalar surface. -/
theorem original_lift : HomotopyLift (simplex P u) parameter
    (boundedFlatCoefficientLaurentUnitPasting P u) := by
  unfold boundedFlatCoefficientLaurentUnitPasting
  exact HomotopyLift.ofLevels (simplex P u) (native_lift P u) _ _ _ _

/-- The whole fixed scalar surface enters the nerve through the original ten full nodes. -/
def nerveParameter : C(I × I,
    |nerve (Codiscrete (CommonReferenceNerve.Node (source P u)))|) :=
  (CommonReferenceNerve.parameter _ (nodes P u)).comp parameter.toContinuousMap

/-- The whole source path retains the shifted composition route and its literal association. -/
theorem nerve_source (s : I) :
    nerveParameter P u (0, s) = CommonReferenceNerve.parameter _ (nodes P u)
      ((V.trans (C1.symm.trans D1)) s) := by
  change CommonReferenceNerve.parameter _ _ (parameter (0, s)) = _
  exact congrArg (CommonReferenceNerve.parameter _ (nodes P u)) (parameter.apply_zero s)

/-- The whole target path retains the lower composition route and its literal association. -/
theorem nerve_target (s : I) :
    nerveParameter P u (1, s) = CommonReferenceNerve.parameter _ (nodes P u)
      (((C0.symm.trans D0).trans W) s) := by
  change CommonReferenceNerve.parameter _ _ (parameter (1, s)) = _
  exact congrArg (CommonReferenceNerve.parameter _ (nodes P u)) (parameter.apply_one s)

/-- Every relative-time point retains the full lower old terminal node. -/
theorem nerve_zero (r : I) :
    nerveParameter P u (r, 0) =
      CommonReferenceNerve.parameter _ (nodes P u) (StdSimplex.single 2) := by
  change CommonReferenceNerve.parameter _ _ (parameter (r, 0)) = _
  rw [Path.Homotopy.source]

/-- Every relative-time point retains the distinct unit-shifted new terminal node. -/
theorem nerve_one (r : I) :
    nerveParameter P u (r, 1) =
      CommonReferenceNerve.parameter _ (nodes P u) (StdSimplex.single 9) := by
  change CommonReferenceNerve.parameter _ _ (parameter (r, 1)) = _
  rw [Path.Homotopy.target]

/-- Compact nerve evaluation recovers the entire chosen native intertwining on every level. -/
theorem nerve_native (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf
      (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (nerveParameter P u) n ((r, s), x) =
      (CoefficientLaurentUnitTrack.squarePasting P u).level n (r, (s, x)) := by
  rw [CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ _
    (nodes P u) (r, s) (parameter (r, s)) rfl, CommonReferenceNerve.prespectrumFamily_eq]
  exact native_lift P u n r s x

/-- The existing original Laurent-square wrapper is recovered with its complete endpoint casts. -/
theorem nerve_original (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf
      (boundedFlatPerfectWaldhausen (space (op P, a))))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (nerveParameter P u) n ((r, s), x) =
      (boundedFlatCoefficientLaurentUnitPasting P u).level n (r, (s, x)) := by
  rw [CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ _
    (nodes P u) (r, s) (parameter (r, s)) rfl, CommonReferenceNerve.prespectrumFamily_eq]
  exact original_lift P u n r s x

end Quillen.PerfectComplexes.CoefficientLaurentUnitPastingLift
