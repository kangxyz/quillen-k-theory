/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonPasting
public import Quillen.Aglib.Topology.Path.ThreeRadialSquaresMapEvaluation

/-!
# Original unreduced tip of the actual polynomial paste

The three selected cube tops retain the one original common-sheet tip. Their literal
half faces give all ten path tops, so evaluation of the unchanged three-square paste
is constant on its entire top. No path or cancellation clock is replaced.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonPastingTop
open CoefficientBassRaw1PolynomialTripleRoutes CoefficientBassRaw1PolynomialTripleFiller
open CoefficientBassRaw1PolynomialCommonPastingPaths
open CoefficientBassRaw1PolynomialCommonPasting
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b : Under R} (f : a ⟶ b) (negative : Bool)
local notation "β" => chartChoice negative
local notation "p₀" => CategoryTheory.NatTrans.app (polynomialUnderCoefficient R) a
local notation "p₁" => CategoryTheory.NatTrans.app (polynomialUnderCoefficient R) b
local notation "q₀" => CategoryTheory.NatTrans.app α a
local notation "q₁" => CategoryTheory.NatTrans.app α b
local notation "m" => CategoryTheory.Functor.map (polynomialUnderFunctor R) f
local notation "l" => CategoryTheory.Functor.map (laurentUnderFunctor R) f
local notation "X₀" => CoefficientBassRaw1PolynomialCommonSheet.carrier P α β f
local notation "t₀" => CoefficientBassRaw1PolynomialPostcomp.tip P p₀ q₀ l β

/-- The complete first selected square retains the original unreduced tip. -/
theorem first_top (r s : I) : firstComparison P α f negative (r, s) 1 = t₀ :=
  extension_top P p₀ q₀ l negative r s

/-- The complete middle square keeps the same tip under its full reference normalization. -/
theorem middle_top (r s : I) : middleComparison P α f negative (r, s) 1 = t₀ := by
  change CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f
    (extension P p₀ m q₁ negative ![r, s, 1]) = t₀
  rw [extension_top]
  exact CoefficientBassPolynomialSheetNormalization.map_tip _ _ _ _ _ _ _

/-- The complete last square keeps the same tip under both rectangle transports. -/
theorem last_top (r s : I) : lastComparison P α f negative (r, s) 1 = t₀ := by
  change CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f
    (extension P f p₁ q₁ negative ![r, s, 1]) = t₀
  rw [extension_top]
  exact CoefficientBassPolynomialSheetNormalization.map_tip _ _ _ _ _ _ _

/-- The original radialA path retains the unreduced tip at every point of its top. -/
theorem radialA_top (r : I) : radialA P α f negative r 1 = t₀ := by
  have h := first_top P α f negative 0 (lower r)
  rw [(firstComparison P α f negative).apply_zero] at h
  exact (congrArg (fun g : C(I, X₀) ↦ g 1)
    (path_lower (radialA P α f negative) (capX P α f negative) r)).symm.trans h

/-- The original radialB path retains the unreduced tip at every point of its top. -/
theorem radialB_top (r : I) : radialB P α f negative r 1 = t₀ := by
  have h := first_top P α f negative 1 (lower r)
  rw [(firstComparison P α f negative).apply_one] at h
  exact (congrArg (fun g : C(I, X₀) ↦ g 1)
    (path_lower (radialB P α f negative) (capY P α f negative) r)).symm.trans h

/-- The original radialC path retains the unreduced tip at every point of its top. -/
theorem radialC_top (r : I) : radialC P α f negative r 1 = t₀ := by
  have h := middle_top P α f negative 0 (lower r)
  rw [(middleComparison P α f negative).apply_zero] at h
  exact (congrArg (fun g : C(I, X₀) ↦ g 1)
    (path_lower (radialC P α f negative) (capW P α f negative) r)).symm.trans h

/-- The original radialD path retains the unreduced tip at every point of its top. -/
theorem radialD_top (r : I) : radialD P α f negative r 1 = t₀ := by
  have h := last_top P α f negative 1 (lower r)
  rw [(lastComparison P α f negative).apply_one] at h
  exact (congrArg (fun g : C(I, X₀) ↦ g 1)
    (path_lower (radialD P α f negative) (capU P α f negative) r)).symm.trans h

/-- The original capX path retains the unreduced tip at every point of its top. -/
theorem capX_top (r : I) : capX P α f negative r 1 = t₀ := by
  have h := first_top P α f negative 0 (upper r)
  rw [(firstComparison P α f negative).apply_zero] at h
  exact (congrArg (fun g : C(I, X₀) ↦ g 1)
    (path_upper (radialA P α f negative) (capX P α f negative) r)).symm.trans h

/-- The original capY path retains the unreduced tip at every point of its top. -/
theorem capY_top (r : I) : capY P α f negative r 1 = t₀ := by
  have h := first_top P α f negative 1 (upper r)
  rw [(firstComparison P α f negative).apply_one] at h
  exact (congrArg (fun g : C(I, X₀) ↦ g 1)
    (path_upper (radialB P α f negative) (capY P α f negative) r)).symm.trans h

/-- The original capZ path retains the unreduced tip at every point of its top. -/
theorem capZ_top (r : I) : capZ P α f negative r 1 = t₀ := by
  have h := middle_top P α f negative 1 (upper r)
  rw [(middleComparison P α f negative).apply_one] at h
  exact (congrArg (fun g : C(I, X₀) ↦ g 1)
    (path_upper (radialB P α f negative) (capZ P α f negative) r)).symm.trans h

/-- The original capW path retains the unreduced tip at every point of its top. -/
theorem capW_top (r : I) : capW P α f negative r 1 = t₀ := by
  have h := middle_top P α f negative 0 (upper r)
  rw [(middleComparison P α f negative).apply_zero] at h
  exact (congrArg (fun g : C(I, X₀) ↦ g 1)
    (path_upper (radialC P α f negative) (capW P α f negative) r)).symm.trans h

/-- The original capV path retains the unreduced tip at every point of its top. -/
theorem capV_top (r : I) : capV P α f negative r 1 = t₀ := by
  have h := last_top P α f negative 0 (upper r)
  rw [(lastComparison P α f negative).apply_zero] at h
  exact (congrArg (fun g : C(I, X₀) ↦ g 1)
    (path_upper (radialC P α f negative) (capV P α f negative) r)).symm.trans h

/-- The original capU path retains the unreduced tip at every point of its top. -/
theorem capU_top (r : I) : capU P α f negative r 1 = t₀ := by
  have h := last_top P α f negative 1 (upper r)
  rw [(lastComparison P α f negative).apply_one] at h
  exact (congrArg (fun g : C(I, X₀) ↦ g 1)
    (path_upper (radialD P α f negative) (capU P α f negative) r)).symm.trans h

/-- Every point of the actual pasted top is the one original common-sheet tip. -/
theorem family_top (r s : I) : family P α f negative ![r, s, 1] = t₀ := by
  let c : Path (PUnit.unit : PUnit.{1}) PUnit.unit := Path.refl _
  let H : (c.trans c).Homotopy (c.trans c) := Path.Homotopy.refl _
  exact Path.Homotopy.ThreeRadialSquares.paste_eval_compare
    (fun g : C(I, X₀) ↦ g 1) (ContinuousMap.const PUnit.{1} t₀)
    (radialA P α f negative) (radialB P α f negative)
    (radialC P α f negative) (radialD P α f negative)
    (capX P α f negative) (capY P α f negative)
    (capZ P α f negative) (capW P α f negative)
    (capV P α f negative) (capU P α f negative)
    c c c c c c c c c c
    (firstComparison P α f negative) (middleComparison P α f negative)
    (lastComparison P α f negative) H H H
    (radialA_top P α f negative) (radialB_top P α f negative)
    (radialC_top P α f negative) (radialD_top P α f negative)
    (capX_top P α f negative) (capY_top P α f negative)
    (capZ_top P α f negative) (capW_top P α f negative)
    (capV_top P α f negative) (capU_top P α f negative)
    (first_top P α f negative) (middle_top P α f negative)
    (last_top P α f negative) r s

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonPastingTop
