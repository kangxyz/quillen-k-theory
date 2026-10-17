/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedChosenJ0Face
public import Quillen.Topology.Path.ProjectionPasteWord

/-! Curry the original selected cube into seed-path space without changing any coordinate. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedChosenPathCube
open CommonReferenceNerve

/-- A whole carrier surface is the original path of seed paths. -/
def surfacePath {X : Type*} [TopologicalSpace X] {f g : C(I, X)}
    (H : f.Homotopy g) : Path f g where
  toContinuousMap := H.curry
  source' := H.curry_zero
  target' := H.curry_one

/-- Currying changes neither coordinate of the original surface. -/
theorem surfacePath_apply {X : Type*} [TopologicalSpace X] {f g : C(I, X)}
    (H : f.Homotopy g) (r s : I) : surfacePath H r s = H (r, s) := rfl

/-- The same original half cut is used by surface concatenation and path concatenation. -/
theorem surfacePath_trans {X : Type*} [TopologicalSpace X] {f g h : C(I, X)}
    (H : f.Homotopy g) (K : g.Homotopy h) :
    surfacePath (H.trans K) = (surfacePath H).trans (surfacePath K) := by
  apply Path.ext
  funext r
  apply ContinuousMap.ext
  intro s
  change H.trans K (r, s) = ((surfacePath H).trans (surfacePath K) r) s
  rw [ContinuousMap.Homotopy.trans_apply, Path.trans_apply]
  split_ifs <;> rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b c : Under R}
  (p : a ⟶ b) (q : b ⟶ c)

/-- The original cube itself, viewed as a comparison of its original route paths. -/
def cubeComparison :
    (surfacePath (CoefficientBassCompositeActualLeftRoute.routeHomotopy P p q)).Homotopy
      (surfacePath (CoefficientBassCompositeActualRightRoute.routeHomotopy P p q)) where
  toContinuousMap := (CoefficientBassCompositeActualMixedFiller.boundary P p q).carrier.curry
  map_zero_left r := by
    apply ContinuousMap.ext
    intro s
    let B := CoefficientBassCompositeActualMixedFiller.boundary P p q
    exact B.extension_face (0, false)
      (CutOpenCarrier.RelativeBoundary.onFace (0, false)
        (CutOpenCarrier.RelativeBoundary.coordinates 0 r s) rfl)
  map_one_left r := by
    apply ContinuousMap.ext
    intro s
    let B := CoefficientBassCompositeActualMixedFiller.boundary P p q
    exact B.extension_face (0, true)
      (CutOpenCarrier.RelativeBoundary.onFace (0, true)
        (CutOpenCarrier.RelativeBoundary.coordinates 1 r s) rfl)
  prop' r t ht := by
    rcases ht with ht | ht
    · subst t
      apply ContinuousMap.ext
      intro s
      exact ((CoefficientBassCompositeActualMixedFiller.boundary P p q).carrier_start r s).trans
        (CoefficientBassCompositeActualLeftRoute.route_start P p q s).symm
    · have ht' : t = 1 := ht
      subst t
      apply ContinuousMap.ext
      intro s
      exact ((CoefficientBassCompositeActualMixedFiller.boundary P p q).carrier_finish r s).trans
        (CoefficientBassCompositeActualLeftRoute.route_finish P p q s).symm

/-- Every point is literally the already selected original cube, with seed time curried last. -/
theorem cubeComparison_apply (r t s : I) :
    cubeComparison P p q (r, t) s =
      (CoefficientBassCompositeActualMixedFiller.boundary P p q).carrier ((r, t), s) := rfl

/-- Retype only route concatenations; the whole original cube interior remains unchanged. -/
def comparison :
    ((surfacePath (CoefficientBassCompositeActualLeftRoute.middle P p q)).trans
      (surfacePath (CoefficientBassCompositeActualLeftRoute.first P p q))).Homotopy
    ((surfacePath (CoefficientBassCompositeActualRightRoute.c0 P p q)).trans
      ((surfacePath
        (CoefficientBassCompositeJ0Conjugation.reverseComparison P p q).toHomotopy).trans
        (surfacePath (CoefficientBassCompositeActualRightRoute.c1 P p q)))) :=
  (cubeComparison P p q).cast
    (surfacePath_trans _ _)
    ((surfacePath_trans _ _).trans
      (congrArg (fun γ ↦ (surfacePath (CoefficientBassCompositeActualRightRoute.c0 P p q)).trans γ)
        (surfacePath_trans _ _)))

/-- Endpoint retyping of the original paths never changes the selected cube's values. -/
theorem comparison_apply (r t s : I) : comparison P p q (r, t) s =
    (CoefficientBassCompositeActualMixedFiller.boundary P p q).carrier ((r, t), s) := rfl

end Quillen.PerfectComplexes.CoefficientBassSeedChosenPathCube
