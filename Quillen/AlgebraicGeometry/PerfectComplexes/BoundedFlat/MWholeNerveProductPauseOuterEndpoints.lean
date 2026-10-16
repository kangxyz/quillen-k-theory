/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPauseOuterFaces

/-!
# Inherited old-map endpoint faces of the actual product pause

The original 140-node cubeLift, precompLift and postcompLift remain literal.
Only their already proved supported boundary subfaces are used here.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeNerve
open BassReferenceMerge BassH0Merge BassH1Join

private theorem coefficient_pause_endpoint (e : Fin 2) (r t : unitInterval) :
    coefficientPauseCube ![r, productEndpointTime e, t] =
      coefficientPauseCube ![0, productEndpointTime e, t] := by
  fin_cases e
  · change ChangedBoundaryPause.cube _ ![r, 0, t] =
      ChangedBoundaryPause.cube _ ![0, 0, t]
    rw [ChangedBoundaryPause.cube_source, ChangedBoundaryPause.cube_source]
  · change ChangedBoundaryPause.cube _ ![r, 1, t] =
      ChangedBoundaryPause.cube _ ![0, 1, t]
    rw [ChangedBoundaryPause.cube_target, ChangedBoundaryPause.cube_target]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- Both original coefficient endpoint faces stay fixed for the whole pause time. -/
theorem polynomial_pause_coefficient_endpoint
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (e : Fin 2) (r s t : unitInterval) :
    polynomialPause P u v w α hc inverse ![r, productEndpointTime e, s, t] =
      polynomialProductPrism P u v w α hc inverse ![productEndpointTime e, s, t] := by
  calc
    _ = polynomialPause P u v w α hc inverse ![0, productEndpointTime e, s, t] := by
      change CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w α hc)
        (Quillen.SimplexGrid.parameter.{u + 1} 17 4
          (coefficientPauseCube ![r, productEndpointTime e, productPolynomialTime inverse t],
        NativeSquareFiveSimplex.parameter s)) = _
      rw [coefficient_pause_endpoint]
      rfl
    _ = _ := polynomial_pause_zero P u v w α hc inverse _ s t

/-- Both original coefficient endpoint faces stay fixed for the whole pause time. -/
theorem chart_pause_coefficient_endpoint
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (e : Fin 2) (r s t : unitInterval) :
    chartPause P u v w α hd inverse ![r, productEndpointTime e, s, t] =
      chartProductPrism P u v w α hd inverse ![productEndpointTime e, s, t] := by
  calc
    _ = chartPause P u v w α hd inverse ![0, productEndpointTime e, s, t] := by
      change CommonReferenceNerve.parameter _ (chartProductNodes P u v w α hd)
        (Quillen.SimplexGrid.parameter.{u + 1} 4 17
          (NativeSquareFiveSimplex.parameter (productPolynomialTime inverse t),
        coefficientPauseCube ![r, productEndpointTime e, s])) = _
      rw [coefficient_pause_endpoint]
      rfl
    _ = _ := chart_pause_zero P u v w α hd inverse _ s t

/-- The whole original source subface retains its literal old cube and anchor. -/
theorem polynomial_pause_plus_old_source (r s t : unitInterval) :
    polynomialPause P u v w (underToLaurent R) (laurentPlus_projection P c)
      false ![r, 0, s, t] =
      cubeLift P (u ≫ v) w (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (h0Anchor P (u ≫ v) w) ![1, upper s, lower t] := by
  exact (polynomial_pause_coefficient_endpoint P u v w
    (underToLaurent R) (laurentPlus_projection P c) false 0 r s t).trans
      (polynomial_product_plus_source_face P u v w s t)

/-- The whole original source subface retains its literal old cube and anchor. -/
theorem polynomial_pause_minus_old_source (r s t : unitInterval) :
    polynomialPause P u v w (underToLaurentInvert R) (laurentMinus_projection P c)
      true ![r, 0, s, t] =
      cubeLift P (u ≫ v) w (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (h0Anchor P (u ≫ v) w) ![1, upper s, upper (upper t)] := by
  exact (polynomial_pause_coefficient_endpoint P u v w
    (underToLaurentInvert R) (laurentMinus_projection P c) true 0 r s t).trans
      (polynomial_product_minus_source_face P u v w s t)

/-- The whole original source subface retains its literal old cube and anchor. -/
theorem chart_pause_plus_old_source (r s t : unitInterval) :
    chartPause P u v w (underToLaurent R) (laurentPlus_projection P d)
      false ![r, 0, s, t] =
      cubeLift P u (v ≫ w) (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (rightStartingAnchor P u v w) ![1, upper s, lower t] := by
  exact (chart_pause_coefficient_endpoint P u v w
    (underToLaurent R) (laurentPlus_projection P d) false 0 r s t).trans
      (chart_product_plus_source_face P u v w s t)

/-- The whole original source subface retains its literal old cube and anchor. -/
theorem chart_pause_minus_old_source (r s t : unitInterval) :
    chartPause P u v w (underToLaurentInvert R) (laurentMinus_projection P d)
      true ![r, 0, s, t] =
      cubeLift P u (v ≫ w) (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (rightStartingAnchor P u v w) ![1, upper s, upper (upper t)] := by
  exact (chart_pause_coefficient_endpoint P u v w
    (underToLaurentInvert R) (laurentMinus_projection P d) true 0 r s t).trans
      (chart_product_minus_source_face P u v w s t)

/-- The old whiskered target subface keeps its original subdivision coordinates. -/
theorem polynomial_pause_plus_old_target (r s t : unitInterval) :
    polynomialPause P u v w (underToLaurent R) (laurentPlus_projection P c)
      false ![r, 1, s, upper t] =
      precompLift P u v w ![1, upper s, lower t] := by
  exact (polynomial_pause_coefficient_endpoint P u v w
    (underToLaurent R) (laurentPlus_projection P c) false 1 r (s) (upper t)).trans
      (polynomial_product_plus_target_face P u v w s t)

/-- The old whiskered target subface keeps its original subdivision coordinates. -/
theorem polynomial_pause_minus_old_target (r s t : unitInterval) :
    polynomialPause P u v w (underToLaurentInvert R) (laurentMinus_projection P c)
      true ![r, 1, s, lower t] =
      precompLift P u v w ![1, upper s, upper (upper t)] := by
  exact (polynomial_pause_coefficient_endpoint P u v w
    (underToLaurentInvert R) (laurentMinus_projection P c) true 1 r (s) (lower t)).trans
      (polynomial_product_minus_target_face P u v w s t)

/-- The old whiskered target subface keeps its original subdivision coordinates. -/
theorem chart_pause_plus_old_target (r s t : unitInterval) :
    chartPause P u v w (underToLaurent R) (laurentPlus_projection P d)
      false ![r, 1, lower s, t] =
      postcompLift P u v w ![1, upper s, lower t] := by
  exact (chart_pause_coefficient_endpoint P u v w
    (underToLaurent R) (laurentPlus_projection P d) false 1 r (lower s) (t)).trans
      (chart_product_plus_target_face P u v w s t)

/-- The old whiskered target subface keeps its original subdivision coordinates. -/
theorem chart_pause_minus_old_target (r s t : unitInterval) :
    chartPause P u v w (underToLaurentInvert R) (laurentMinus_projection P d)
      true ![r, 1, lower s, t] =
      postcompLift P u v w ![1, upper s, upper (upper t)] := by
  exact (chart_pause_coefficient_endpoint P u v w
    (underToLaurentInvert R) (laurentMinus_projection P d) true 1 r (lower s) (t)).trans
      (chart_product_minus_target_face P u v w s t)

/-- The remaining target pieces share their actual full-reference middle face. -/
theorem product_pause_plus_middle (r s t : unitInterval) :
    polynomialPause P u v w (underToLaurent R) (laurentPlus_projection P c)
      false ![r, 1, s, lower t] =
    chartPause P u v w (underToLaurent R) (laurentPlus_projection P d)
      false ![r, 1, upper s, t] := by
  exact (polynomial_pause_coefficient_endpoint P u v w
    (underToLaurent R) (laurentPlus_projection P c) false 1 r s (lower t)).trans
      ((product_plus_middle_face P u v w s t).trans
        (chart_pause_coefficient_endpoint P u v w
          (underToLaurent R) (laurentPlus_projection P d) false 1 r (upper s) t).symm)

/-- The remaining target pieces share their actual full-reference middle face. -/
theorem product_pause_minus_middle (r s t : unitInterval) :
    polynomialPause P u v w (underToLaurentInvert R) (laurentMinus_projection P c)
      true ![r, 1, s, upper t] =
    chartPause P u v w (underToLaurentInvert R) (laurentMinus_projection P d)
      true ![r, 1, upper s, t] := by
  exact (polynomial_pause_coefficient_endpoint P u v w
    (underToLaurentInvert R) (laurentMinus_projection P c) true 1 r s (upper t)).trans
      ((product_minus_middle_face P u v w s t).trans
        (chart_pause_coefficient_endpoint P u v w
          (underToLaurentInvert R) (laurentMinus_projection P d) true 1 r (upper s) t).symm)

end Quillen.PerfectComplexes.BassMWholeNerve
