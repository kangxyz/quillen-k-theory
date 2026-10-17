/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialTriplePathHomotopy
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonRadialSeams

/-! The ten unchanged paths of the actual three-triple polynomial pasting. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonPastingPaths
open CoefficientBassRaw1PolynomialTripleRoutes CoefficientBassRaw1PolynomialTriplePathHomotopy
open CoefficientBassRaw1PolynomialCommonRadialCaps
open CoefficientBassRaw1PolynomialCommonRadialSeams
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

/-- The four original radial matrices in their common full reference. -/
def aMatrix := firstLeft P α β f
/-- The original first right radial matrix in the common full reference. -/
def bMatrix := firstRight P α β f
/-- The original middle left radial matrix with its full reference normalization. -/
def cMatrix := middleLeft P α β f
/-- The original last right radial matrix with both full rectangle transports. -/
def dMatrix := lastRight P α β f

/-- The original first postcomposition cap. -/
def xMatrix : C(I × I, X₀) := postCap P p₀ q₀ l negative
/-- The original first input cap. -/
def yMatrix : C(I × I, X₀) :=
  CoefficientBassRaw1PolynomialInputCap.placedFamily P β p₀ q₀ l
/-- The original middle input cap with its complete rectangle reanchor. -/
def zMatrix : C(I × I, X₀) :=
  (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f).comp
    (CoefficientBassRaw1PolynomialInputCap.placedFamily P β p₀ m q₁)
/-- The original middle postcomposition cap with the same reanchor. -/
def wMatrix : C(I × I, X₀) :=
  (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f).comp
    (postCap P p₀ m q₁ negative)
/-- The original last postcomposition cap retains both rectangle transports. -/
def vMatrix : C(I × I, X₀) :=
  (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f).comp
    (postCap P f p₁ q₁ negative)
/-- The original last input cap retains both rectangle transports. -/
def uMatrix : C(I × I, X₀) :=
  (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f).comp
    (CoefficientBassRaw1PolynomialInputCap.placedFamily P β f p₁ q₁)

/-- The common radial source is retained pointwise at every height. -/
theorem ab_zero (h : I) : aMatrix P α f negative (0,h) = bMatrix P α f negative (0,h) := by
  have he := start P p₀ q₀ l negative h
  dsimp only [left, right] at he
  rw [ScalarRectangle.concatFirst_zero, ScalarRectangle.concatFirst_zero] at he
  exact he

/-- The middle radial source agrees before any native evaluation. -/
theorem cb_zero (h : I) : cMatrix P α f negative (0,h) = bMatrix P α f negative (0,h) := by
  have he := start P p₀ m q₁ negative h
  dsimp only [left, right] at he
  rw [ScalarRectangle.concatFirst_zero, ScalarRectangle.concatFirst_zero] at he
  have hm := congrArg (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f) he
  exact hm.trans (DFunLike.congr_fun (first_right_eq_middle_right P α β f) (0,h)).symm

/-- The final radial source has the same complete direct word. -/
theorem dc_zero (h : I) : dMatrix P α f negative (0,h) = cMatrix P α f negative (0,h) := by
  have he := start P f p₁ q₁ negative h
  dsimp only [left, right] at he
  rw [ScalarRectangle.concatFirst_zero, ScalarRectangle.concatFirst_zero] at he
  have hm := congrArg (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f) he.symm
  exact hm.trans (DFunLike.congr_fun (middle_left_eq_last_left P α β f) (0,h)).symm

/-- The original ax whole cap join. -/
theorem ax_join (h : I) : aMatrix P α f negative (1,h) =
    xMatrix P α f negative (0,h) := by
  exact left_join P p₀ q₀ l negative h

/-- The original by whole cap join. -/
theorem by_join (h : I) : bMatrix P α f negative (1,h) =
    yMatrix P α f negative (0,h) := by
  exact right_join P p₀ q₀ l negative h

/-- The original cw whole cap join. -/
theorem cw_join (h : I) : cMatrix P α f negative (1,h) =
    wMatrix P α f negative (0,h) := by
  have he := congrArg (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f)
    (left_join P p₀ m q₁ negative h)
  exact he

/-- The original bz whole cap join. -/
theorem bz_join (h : I) : bMatrix P α f negative (1,h) =
    zMatrix P α f negative (0,h) := by
  have he := congrArg (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f)
    (right_join P p₀ m q₁ negative h)
  exact (DFunLike.congr_fun (first_right_eq_middle_right P α β f) (1,h)).trans he

/-- The original cv whole cap join. -/
theorem cv_join (h : I) : cMatrix P α f negative (1,h) =
    vMatrix P α f negative (0,h) := by
  have he := congrArg (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f)
    (left_join P f p₁ q₁ negative h)
  exact (DFunLike.congr_fun (middle_left_eq_last_left P α β f) (1,h)).trans he

/-- The original du whole cap join. -/
theorem du_join (h : I) : dMatrix P α f negative (1,h) =
    uMatrix P α f negative (0,h) := by
  have he := congrArg (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f)
    (right_join P f p₁ q₁ negative h)
  exact he

/-- Both original xy cap ends are the same full composite word. -/
theorem xy_one (h : I) : xMatrix P α f negative (1,h) =
    yMatrix P α f negative (1,h) := by
  have he := finish P p₀ q₀ l negative h
  dsimp only [left, right] at he
  rw [ScalarRectangle.concatFirst_one, ScalarRectangle.concatFirst_one] at he
  exact he

/-- Both original wz cap ends are the same full composite word. -/
theorem wz_one (h : I) : wMatrix P α f negative (1,h) =
    zMatrix P α f negative (1,h) := by
  have he := finish P p₀ m q₁ negative h
  dsimp only [left, right] at he
  rw [ScalarRectangle.concatFirst_one, ScalarRectangle.concatFirst_one] at he
  exact congrArg (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f) he

/-- Both original vu cap ends are the same full composite word. -/
theorem vu_one (h : I) : vMatrix P α f negative (1,h) =
    uMatrix P α f negative (1,h) := by
  have he := finish P f p₁ q₁ negative h
  dsimp only [left, right] at he
  rw [ScalarRectangle.concatFirst_one, ScalarRectangle.concatFirst_one] at he
  exact congrArg (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f) he

/-- Endpoint rows are continuous functions of the independent original height. -/
def row (M : C(I × I, X₀)) (r : I) : C(I, X₀) := ContinuousMap.curry M r

/-- The common source for all four radial paths. -/
def origin := row P α f negative (aMatrix P α f negative) 0
/-- The original radial A path. -/
def radialA : Path (origin P α f negative)
    (row P α f negative (aMatrix P α f negative) 1) :=
  heightPath (aMatrix P α f negative) _ _ (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- The original radial B path. -/
def radialB : Path (origin P α f negative)
    (row P α f negative (bMatrix P α f negative) 1) :=
  heightPath (bMatrix P α f negative) _ _
    (fun h ↦ (ab_zero P α f negative h).symm) (fun _ ↦ rfl)

/-- The original radial C path. -/
def radialC : Path (origin P α f negative)
    (row P α f negative (cMatrix P α f negative) 1) :=
  heightPath (cMatrix P α f negative) _ _
    (fun h ↦ (cb_zero P α f negative h).trans (ab_zero P α f negative h).symm)
    (fun _ ↦ rfl)

/-- The original radial D path. -/
def radialD : Path (origin P α f negative)
    (row P α f negative (dMatrix P α f negative) 1) :=
  heightPath (dMatrix P α f negative) _ _ (fun h ↦ (dc_zero P α f negative h).trans
      ((cb_zero P α f negative h).trans (ab_zero P α f negative h).symm)) (fun _ ↦ rfl)

/-- The original cap X path, retaining its entire height boundary. -/
def capX : Path (row P α f negative (aMatrix P α f negative) 1)
    (row P α f negative (xMatrix P α f negative) 1) :=
  heightPath (xMatrix P α f negative) _ _
    (fun h ↦ (ax_join P α f negative h).symm) (fun _ ↦ rfl)

/-- The original cap Y path, retaining its entire height boundary. -/
def capY : Path (row P α f negative (bMatrix P α f negative) 1)
    (row P α f negative (xMatrix P α f negative) 1) :=
  heightPath (yMatrix P α f negative) _ _
    (fun h ↦ (by_join P α f negative h).symm) (fun h ↦ (xy_one P α f negative h).symm)

/-- The original cap Z path, retaining its entire height boundary. -/
def capZ : Path (row P α f negative (bMatrix P α f negative) 1)
    (row P α f negative (wMatrix P α f negative) 1) :=
  heightPath (zMatrix P α f negative) _ _
    (fun h ↦ (bz_join P α f negative h).symm) (fun h ↦ (wz_one P α f negative h).symm)

/-- The original cap W path, retaining its entire height boundary. -/
def capW : Path (row P α f negative (cMatrix P α f negative) 1)
    (row P α f negative (wMatrix P α f negative) 1) :=
  heightPath (wMatrix P α f negative) _ _
    (fun h ↦ (cw_join P α f negative h).symm) (fun _ ↦ rfl)

/-- The original cap V path, retaining its entire height boundary. -/
def capV : Path (row P α f negative (cMatrix P α f negative) 1)
    (row P α f negative (vMatrix P α f negative) 1) :=
  heightPath (vMatrix P α f negative) _ _
    (fun h ↦ (cv_join P α f negative h).symm) (fun _ ↦ rfl)

/-- The original cap U path, retaining its entire height boundary. -/
def capU : Path (row P α f negative (dMatrix P α f negative) 1)
    (row P α f negative (vMatrix P α f negative) 1) :=
  heightPath (uMatrix P α f negative) _ _
    (fun h ↦ (du_join P α f negative h).symm) (fun h ↦ (vu_one P α f negative h).symm)

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonPastingPaths
