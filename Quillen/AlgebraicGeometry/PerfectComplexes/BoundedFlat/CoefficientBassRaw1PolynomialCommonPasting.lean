/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCommonPastingPaths
public import Quillen.Aglib.Topology.Path.ThreeRadialSquares

/-! Pasting the three actual fixed-boundary polynomial cap cubes. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonPasting
open CoefficientBassRaw1PolynomialTripleRoutes CoefficientBassRaw1PolynomialTripleFiller
open CoefficientBassRaw1PolynomialTriplePathHomotopy CoefficientBassRaw1PolynomialCommonPastingPaths
open CoefficientBassRaw1PolynomialCommonRadialSeams

/-- A fixed-end cube gives a path homotopy without changing any scalar coordinate. -/
def comparisonOfCube {X : Type*} [TopologicalSpace X] {a b : C(I, X)}
    (F : C(Fin 3 → I, X)) (L R : Path a b)
    (h0 : ∀ r h, F ![0, r, h] = L r h) (h1 : ∀ r h, F ![1, r, h] = R r h)
    (hs : ∀ s h, F ![s, 0, h] = F ![0, 0, h])
    (ht : ∀ s h, F ![s, 1, h] = F ![0, 1, h]) : L.Homotopy R where
  toContinuousMap := heightCube F
  map_zero_left r := ContinuousMap.ext (h0 r)
  map_one_left r := ContinuousMap.ext (h1 r)
  prop' s r hr := by
    rcases hr with rfl | rfl
    · exact ContinuousMap.ext (fun h ↦ (hs s h).trans (h0 0 h))
    · exact ContinuousMap.ext (fun h ↦ (ht s h).trans (h0 1 h))

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

/-- The unchanged first actual triple cube. -/
def firstCube : C(Fin 3 → I, X₀) := extension P p₀ q₀ l negative
/-- The unchanged middle cube under its full polynomial-reference normalization. -/
def middleCube : C(Fin 3 → I, X₀) :=
  (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f).comp
    (extension P p₀ m q₁ negative)
/-- The unchanged last cube under both full rectangle transports. -/
def lastCube : C(Fin 3 → I, X₀) :=
  (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f).comp
    (extension P f p₁ q₁ negative)

/-- The original first comparison is retained, including its selected interior. -/
def firstComparison :
    ((radialA P α f negative).trans (capX P α f negative)).Homotopy
      ((radialB P α f negative).trans (capY P α f negative)) :=
  comparison P p₀ q₀ l negative

/-- The complete middle zero face has the original two half clocks. -/
theorem middle_zero (r h : I) :
    middleCube P α f negative ![0, r, h] =
      ((radialC P α f negative).trans (capW P α f negative) r) h := by
  obtain ⟨t, rfl⟩ | ⟨t, rfl⟩ := cover r
  · rw [path_lower]
    have he := extension_zero P p₀ m q₁ negative (lower t) h
    have hc := ScalarRectangle.concatFirst_lower
      (CoefficientBassRaw1PolynomialRadialCaps.left P β p₀ m q₁)
      (postCap P p₀ m q₁ negative) (left_join P p₀ m q₁ negative) t h
    have hm := congrArg (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f)
      (he.trans hc)
    exact hm
  · rw [path_upper]
    have he := extension_zero P p₀ m q₁ negative (upper t) h
    have hc := ScalarRectangle.concatFirst_upper
      (CoefficientBassRaw1PolynomialRadialCaps.left P β p₀ m q₁)
      (postCap P p₀ m q₁ negative) (left_join P p₀ m q₁ negative) t h
    have hm := congrArg (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f)
      (he.trans hc)
    exact hm

/-- The complete middle one face has the original two half clocks. -/
theorem middle_one (r h : I) :
    middleCube P α f negative ![1, r, h] =
      ((radialB P α f negative).trans (capZ P α f negative) r) h := by
  obtain ⟨t, rfl⟩ | ⟨t, rfl⟩ := cover r
  · rw [path_lower]
    have he := extension_one P p₀ m q₁ negative (lower t) h
    have hc := ScalarRectangle.concatFirst_lower
      (CoefficientBassRaw1PolynomialRadialCaps.right P β p₀ m q₁)
      (CoefficientBassRaw1PolynomialInputCap.placedFamily P β p₀ m q₁)
      (right_join P p₀ m q₁ negative) t h
    have hm := congrArg (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f)
      (he.trans hc)
    exact hm.trans (DFunLike.congr_fun
      (first_right_eq_middle_right P α β f) (t, h)).symm
  · rw [path_upper]
    have he := extension_one P p₀ m q₁ negative (upper t) h
    have hc := ScalarRectangle.concatFirst_upper
      (CoefficientBassRaw1PolynomialRadialCaps.right P β p₀ m q₁)
      (CoefficientBassRaw1PolynomialInputCap.placedFamily P β p₀ m q₁)
      (right_join P p₀ m q₁ negative) t h
    have hm := congrArg (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f)
      (he.trans hc)
    exact hm

/-- The whole original middle cube is used as the prescribed radial square. -/
def middleComparison :
    ((radialC P α f negative).trans (capW P α f negative)).Homotopy
      ((radialB P α f negative).trans (capZ P α f negative)) :=
  comparisonOfCube (middleCube P α f negative) _ _
    (middle_zero P α f negative) (middle_one P α f negative)
    (fun s h ↦ congrArg (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f)
      ((extension_route_zero P p₀ m q₁ negative s h).trans
        (extension_route_zero P p₀ m q₁ negative 0 h).symm))
    (fun s h ↦ congrArg (CoefficientBassRaw1PolynomialCommonSheet.middleMap P α β f)
      ((extension_route_one P p₀ m q₁ negative s h).trans
        (extension_route_one P p₀ m q₁ negative 0 h).symm))

/-- The complete last zero face has the original two half clocks. -/
theorem last_zero (r h : I) :
    lastCube P α f negative ![0, r, h] =
      ((radialC P α f negative).trans (capV P α f negative) r) h := by
  obtain ⟨t, rfl⟩ | ⟨t, rfl⟩ := cover r
  · rw [path_lower]
    have he := extension_zero P f p₁ q₁ negative (lower t) h
    have hc := ScalarRectangle.concatFirst_lower
      (CoefficientBassRaw1PolynomialRadialCaps.left P β f p₁ q₁)
      (postCap P f p₁ q₁ negative) (left_join P f p₁ q₁ negative) t h
    have hm := congrArg (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f)
      (he.trans hc)
    exact hm.trans (DFunLike.congr_fun
      (middle_left_eq_last_left P α β f) (t, h)).symm
  · rw [path_upper]
    have he := extension_zero P f p₁ q₁ negative (upper t) h
    have hc := ScalarRectangle.concatFirst_upper
      (CoefficientBassRaw1PolynomialRadialCaps.left P β f p₁ q₁)
      (postCap P f p₁ q₁ negative) (left_join P f p₁ q₁ negative) t h
    have hm := congrArg (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f)
      (he.trans hc)
    exact hm

/-- The complete last one face has the original two half clocks. -/
theorem last_one (r h : I) :
    lastCube P α f negative ![1, r, h] =
      ((radialD P α f negative).trans (capU P α f negative) r) h := by
  obtain ⟨t, rfl⟩ | ⟨t, rfl⟩ := cover r
  · rw [path_lower]
    have he := extension_one P f p₁ q₁ negative (lower t) h
    have hc := ScalarRectangle.concatFirst_lower
      (CoefficientBassRaw1PolynomialRadialCaps.right P β f p₁ q₁)
      (CoefficientBassRaw1PolynomialInputCap.placedFamily P β f p₁ q₁)
      (right_join P f p₁ q₁ negative) t h
    have hm := congrArg (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f)
      (he.trans hc)
    exact hm
  · rw [path_upper]
    have he := extension_one P f p₁ q₁ negative (upper t) h
    have hc := ScalarRectangle.concatFirst_upper
      (CoefficientBassRaw1PolynomialRadialCaps.right P β f p₁ q₁)
      (CoefficientBassRaw1PolynomialInputCap.placedFamily P β f p₁ q₁)
      (right_join P f p₁ q₁ negative) t h
    have hm := congrArg (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f)
      (he.trans hc)
    exact hm

/-- The whole original last cube is used as the prescribed radial square. -/
def lastComparison :
    ((radialC P α f negative).trans (capV P α f negative)).Homotopy
      ((radialD P α f negative).trans (capU P α f negative)) :=
  comparisonOfCube (lastCube P α f negative) _ _
    (last_zero P α f negative) (last_one P α f negative)
    (fun s h ↦ congrArg (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f)
      ((extension_route_zero P f p₁ q₁ negative s h).trans
        (extension_route_zero P f p₁ q₁ negative 0 h).symm))
    (fun s h ↦ congrArg (CoefficientBassRaw1PolynomialCommonSheet.lastMap P α β f)
      ((extension_route_one P f p₁ q₁ negative s h).trans
        (extension_route_one P f p₁ q₁ negative 0 h).symm))

/-- The original two-piece left cap word. -/
def leftWord := ((capY P α f negative).symm.trans (capZ P α f negative)).trans
  ((capW P α f negative).symm.trans (capV P α f negative))

/-- The original opposite cap word retains its nested radial and input clocks. -/
def rightWord := (capX P α f negative).symm.trans
  (((radialA P α f negative).symm.trans (radialD P α f negative)).trans
    (capU P α f negative))

/-- The fixed three-radial-square recipe pastes the three chosen actual cube interiors. -/
def pasted : (leftWord P α f negative).Homotopy (rightWord P α f negative) :=
  Path.Homotopy.ThreeRadialSquares.paste
    (radialA P α f negative) (radialB P α f negative)
    (radialC P α f negative) (radialD P α f negative)
    (capX P α f negative) (capY P α f negative)
    (capZ P α f negative) (capW P α f negative)
    (capV P α f negative) (capU P α f negative)
    (firstComparison P α f negative) (middleComparison P α f negative)
    (lastComparison P α f negative)

/-- The independent original height is uncurried after the exact path-pasting recipe. -/
def family : C(Fin 3 → I, X₀) :=
  (ContinuousMap.uncurry (pasted P α f negative).toHomotopy.toContinuousMap).comp
    ⟨fun z ↦ ((z 0, z 1), z 2), by fun_prop⟩

/-- The first whole boundary word is unchanged. -/
theorem family_zero (r h : I) : family P α f negative ![0, r, h] =
    leftWord P α f negative r h :=
  congrArg (fun g : C(I, X₀) ↦ g h) ((pasted P α f negative).apply_zero r)

/-- The opposite whole boundary word is unchanged. -/
theorem family_one (r h : I) : family P α f negative ![1, r, h] =
    rightWord P α f negative r h :=
  congrArg (fun g : C(I, X₀) ↦ g h) ((pasted P α f negative).apply_one r)

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialCommonPasting
