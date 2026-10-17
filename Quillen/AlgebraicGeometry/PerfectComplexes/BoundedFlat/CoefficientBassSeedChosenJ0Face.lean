/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedChosenChartEdge
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCompositeJ0ConjugationTransport

/-! The two original chosen cubes have exactly the transported common J0 quarter face. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedChosenJ0Face
open CommonReferenceNerve Quillen.NativePathCells

private theorem trans_lower {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g h : C(X, Y)} (H : f.Homotopy g) (K : g.Homotopy h) (s : I) (x : X) :
    H.trans K (lower s, x) = H (s, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  split
  · change H (⟨2 * (lower s : ℝ), _⟩, x) = H (s, x)
    exact congrArg (fun t : I ↦ H (t, x)) (Subtype.ext (by dsimp [lower]; ring))
  · rename_i hs
    exfalso
    apply hs
    change (s : ℝ) / 2 ≤ 1 / 2
    linarith [s.2.2]

private theorem trans_upper {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g h : C(X, Y)} (H : f.Homotopy g) (K : g.Homotopy h) (s : I) (x : X) :
    H.trans K (upper s, x) = K (s, x) := by
  rw [ContinuousMap.Homotopy.trans_apply]
  split
  · rename_i hs
    have hs₀ : s = 0 := by
      apply Subtype.ext
      change ((s : ℝ) + 1) / 2 ≤ 1 / 2 at hs
      change (s : ℝ) = 0
      linarith [s.2.1]
    subst s
    change H (⟨2 * (upper 0 : ℝ), _⟩, x) = K (0, x)
    calc
      _ = H (1, x) := congrArg (fun t : I ↦ H (t, x))
        (Subtype.ext (by norm_num [upper]))
      _ = _ := (H.apply_one x).trans (K.apply_zero x).symm
  · change K (⟨2 * (upper s : ℝ) - 1, _⟩, x) = K (s, x)
    exact congrArg (fun t : I ↦ K (t, x)) (Subtype.ext (by dsimp [upper]; ring))

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b b' c : Under R} (p : a ⟶ b) (q : b ⟶ c)

/-- The original middle quarter is exactly the fixed J0 comparison, including its endpoints. -/
theorem route_middle (r s : I) :
    CoefficientBassCompositeActualRightRoute.route P p q (upper (lower r), s) =
      CoefficientBassCompositeJ0Conjugation.reverseComparison P p q (r, s) :=
  (trans_upper (CoefficientBassCompositeActualRightRoute.c0 P p q)
    ((CoefficientBassCompositeJ0Conjugation.reverseComparison P p q).toHomotopy.trans
      (CoefficientBassCompositeActualRightRoute.c1 P p q)) (lower r) s).trans
    (trans_lower (CoefficientBassCompositeJ0Conjugation.reverseComparison P p q).toHomotopy
      (CoefficientBassCompositeActualRightRoute.c1 P p q) r s)

/-- This entire quarter is the literal right face of the original selected cube. -/
theorem chosen_j0_face (r s : I) :
    (CoefficientBassCompositeActualMixedFiller.boundary P p q).carrier
      ((1, upper (lower r)), s) =
      CoefficientBassCompositeJ0Conjugation.reverseComparison P p q (r, s) := by
  let B := CoefficientBassCompositeActualMixedFiller.boundary P p q
  have hf := B.extension_face (0, true)
    (CutOpenCarrier.RelativeBoundary.onFace (0, true)
      (CutOpenCarrier.RelativeBoundary.coordinates 1 (upper (lower r)) s) rfl)
  exact hf.trans (route_middle P p q r s)

/-- Equal composites identify the full prescribed J0 faces of the two unchanged chosen cubes. -/
theorem chosen_shared_j0 (p' : a ⟶ b') (q' : b' ⟶ c)
    (h : p ≫ q = p' ≫ q') (r s : I) :
    CoefficientBassNegativeCarrierReference.transport P p q p' q' h
      ((CoefficientBassCompositeActualMixedFiller.boundary P p q).carrier
        ((1, upper (lower r)), s)) =
      (CoefficientBassCompositeActualMixedFiller.boundary P p' q').carrier
        ((1, upper (lower r)), s) :=
  (congrArg (CoefficientBassNegativeCarrierReference.transport P p q p' q' h)
    (chosen_j0_face P p q r s)).trans
    ((CoefficientBassCompositeJ0ConjugationTransport.reverseComparison_transport
      P p q p' q' h r s).trans (chosen_j0_face P p' q' r s).symm)

end Quillen.PerfectComplexes.CoefficientBassSeedChosenJ0Face
