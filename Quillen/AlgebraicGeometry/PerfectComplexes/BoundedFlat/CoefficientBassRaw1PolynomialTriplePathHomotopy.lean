/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialTripleFillerFaces

/-! The actual triple cap comparison in the compact height mapping space. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTriplePathHomotopy
open CoefficientBassRaw1PolynomialTripleRoutes CoefficientBassRaw1PolynomialTripleFiller

/-- Keep the original height as the compact mapping-space coordinate. -/
def heightPath {X : Type*} [TopologicalSpace X] (M : C(I × I, X))
    (a b : C(I, X)) (h0 : ∀ h, M (0, h) = a h) (h1 : ∀ h, M (1, h) = b h) :
    Path a b where
  toContinuousMap := ContinuousMap.curry M
  source' := ContinuousMap.ext h0
  target' := ContinuousMap.ext h1

/-- The whole cube is curried without changing any of its three coordinates. -/
def heightCube {X : Type*} [TopologicalSpace X] (E : C(Fin 3 → I, X)) :
    C(I × I, C(I, X)) := ContinuousMap.curry
  ⟨fun z : (I × I) × I ↦ E ![z.1.1, z.1.2, z.2], E.continuous.comp (by fun_prop)⟩

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d) (negative : Bool)
local notation "β" => chartChoice negative
local notation "X" => CoefficientBassRaw1PolynomialPostcomp.carrier P p q w β

/-- The original common direct word is the radial source. -/
def source : C(I, X) := ContinuousMap.curry
  (CoefficientBassRaw1PolynomialRadialCaps.left P β p q w) 0

/-- The original left binary composite word. -/
def leftMiddle : C(I, X) := ContinuousMap.curry
  (CoefficientBassRaw1PolynomialRadialCaps.left P β p q w) 1

/-- The original right binary composite word. -/
def rightMiddle : C(I, X) := ContinuousMap.curry
  (CoefficientBassRaw1PolynomialRadialCaps.right P β p q w) 1

/-- The complete three-map word, with all original pauses. -/
def terminal : C(I, X) := ContinuousMap.curry (postCap P p q w negative) 1

/-- The left radial path keeps its original corrected cap. -/
def leftRadial : Path (source P p q w negative) (leftMiddle P p q w negative) :=
  heightPath (CoefficientBassRaw1PolynomialRadialCaps.left P β p q w) _ _
    (fun _ ↦ rfl) (fun _ ↦ rfl)

/-- The right radial path shares the complete checked direct word. -/
def rightRadial : Path (source P p q w negative) (rightMiddle P p q w negative) :=
  heightPath (CoefficientBassRaw1PolynomialRadialCaps.right P β p q w) _ _
    (fun h ↦ by
      have hs := start P p q w negative h
      dsimp only [left, right] at hs
      rw [ScalarRectangle.concatFirst_zero, ScalarRectangle.concatFirst_zero] at hs
      exact hs.symm) (fun _ ↦ rfl)

/-- Postcomposition is the second half of the left route. -/
def postPath : Path (leftMiddle P p q w negative) (terminal P p q w negative) :=
  heightPath (postCap P p q w negative) _ _
    (fun h ↦ (left_join P p q w negative h).symm) (fun _ ↦ rfl)

/-- The original input-side action is the second half of the right route. -/
def inputPath : Path (rightMiddle P p q w negative) (terminal P p q w negative) :=
  heightPath (CoefficientBassRaw1PolynomialInputCap.placedFamily P β p q w) _ _
    (fun h ↦ (right_join P p q w negative h).symm) (fun h ↦ by
      have ht := finish P p q w negative h
      dsimp only [left, right] at ht
      rw [ScalarRectangle.concatFirst_one, ScalarRectangle.concatFirst_one] at ht
      exact ht.symm)

/-- Path concatenation has exactly the fixed scalar half clock. -/
theorem leftWord_apply (r h : I) :
    ((leftRadial P p q w negative).trans (postPath P p q w negative) r) h =
      left P p q w negative (r, h) := by
  obtain ⟨t, rfl⟩ | ⟨t, rfl⟩ := cover r
  · rw [path_lower]
    exact (ScalarRectangle.concatFirst_lower
      (CoefficientBassRaw1PolynomialRadialCaps.left P β p q w)
      (postCap P p q w negative) (left_join P p q w negative) t h).symm
  · rw [path_upper]
    exact (ScalarRectangle.concatFirst_upper
      (CoefficientBassRaw1PolynomialRadialCaps.left P β p q w)
      (postCap P p q w negative) (left_join P p q w negative) t h).symm

/-- The second path concatenation retains its independent original half clock. -/
theorem rightWord_apply (r h : I) :
    ((rightRadial P p q w negative).trans (inputPath P p q w negative) r) h =
      right P p q w negative (r, h) := by
  obtain ⟨t, rfl⟩ | ⟨t, rfl⟩ := cover r
  · rw [path_lower]
    exact (ScalarRectangle.concatFirst_lower
      (CoefficientBassRaw1PolynomialRadialCaps.right P β p q w)
      (CoefficientBassRaw1PolynomialInputCap.placedFamily P β p q w)
      (right_join P p q w negative) t h).symm
  · rw [path_upper]
    exact (ScalarRectangle.concatFirst_upper
      (CoefficientBassRaw1PolynomialRadialCaps.right P β p q w)
      (CoefficientBassRaw1PolynomialInputCap.placedFamily P β p q w)
      (right_join P p q w negative) t h).symm

/-- The already chosen actual cube is a relative path comparison, with no new filler choice. -/
def comparison :
    ((leftRadial P p q w negative).trans (postPath P p q w negative)).Homotopy
      ((rightRadial P p q w negative).trans (inputPath P p q w negative)) where
  toContinuousMap := heightCube (extension P p q w negative)
  map_zero_left r := by
    ext h
    exact (extension_zero P p q w negative r h).trans (leftWord_apply P p q w negative r h).symm
  map_one_left r := by
    ext h
    exact (extension_one P p q w negative r h).trans (rightWord_apply P p q w negative r h).symm
  prop' s r hr := by
    rcases hr with rfl | rfl
    · ext h
      exact (extension_route_zero P p q w negative s h).trans
        (leftWord_apply P p q w negative 0 h).symm
    · ext h
      exact (extension_route_one P p q w negative s h).trans
        (leftWord_apply P p q w negative 1 h).symm

/-- All three coordinates still evaluate to the exact selected cube. -/
theorem comparison_apply (s r h : I) : comparison P p q w negative (s, r) h =
    extension P p q w negative ![s, r, h] := rfl

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTriplePathHomotopy
