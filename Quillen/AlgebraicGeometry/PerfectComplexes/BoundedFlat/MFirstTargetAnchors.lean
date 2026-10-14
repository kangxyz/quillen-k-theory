/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MFirstTargetRows

/-! Actual anchor joins for the first and last paths of the original reassociation boundary. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMOuterJoin
open BassH0Merge BassH1Join BassMComponents BassMReferences
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The plus target corner is shared through the proved whole original chart edge. -/
theorem plus_target_corner :
    movingNodes P u v (underToLaurent R) (laurentPlus_projection P c) 17 =
    BassH1References.chartNodes P u v (underToLaurent R) (laurentPlus_projection P b)
      (Quillen.SimplexGrid.index 4 4 (2, 4)) :=
  (plus_side_nodes P u v 2).trans
    (product_old_chart_word_nodes P u v (underToLaurent R)
      (laurentPlus_projection P a) (laurentPlus_projection P b) (laurentPlus_projection P c) 4).symm

/-- The complete plus first target row retains all full original node references. -/
theorem plus_first_target_nodes (i : Fin 3) :
    movingNodes P u v (underToLaurent R) (laurentPlus_projection P c)
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
    BassH1References.chartNodes P u v (underToLaurent R) (laurentPlus_projection P b)
      (Quillen.SimplexGrid.index 4 4 (NativeSquareFiveSimplex.firstFace.toOrderHom i, 4)) :=
  post_families_match (BassOverlap.commonReference P u v) (targetPost P v (underToLaurent R))
    (CoefficientSquareFamilies.polynomialSource P u)
    (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map u)) (polynomialProjection P a))
    (moving_first_target_row P u v (underToLaurent R) (laurentPlus_projection P c))
    (product_first_target_row P u v (underToLaurent R) (laurentPlus_projection P b))
    2 (plus_target_corner P u v) i

/-- The full plus target centre, with concrete original node labels. -/
theorem plus_target_center :
    movingNodes P u v (underToLaurent R) (laurentPlus_projection P c) 5 =
    BassH1References.chartNodes P u v (underToLaurent R) (laurentPlus_projection P b) 4 :=
  plus_first_target_nodes P u v 0

/-- The minus target corner is shared through the proved whole original chart edge. -/
theorem minus_target_corner :
    movingNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c) 17 =
    BassH1References.chartNodes P u v (underToLaurentInvert R) (laurentMinus_projection P b)
      (Quillen.SimplexGrid.index 4 4 (2, 4)) :=
  (minus_side_nodes P u v 2).trans
    (product_old_chart_word_nodes P u v (underToLaurentInvert R)
      (laurentMinus_projection P a) (laurentMinus_projection P b)
      (laurentMinus_projection P c) 4).symm

/-- The complete minus first target row retains all full original node references. -/
theorem minus_first_target_nodes (i : Fin 3) :
    movingNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c)
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
    BassH1References.chartNodes P u v (underToLaurentInvert R) (laurentMinus_projection P b)
      (Quillen.SimplexGrid.index 4 4 (NativeSquareFiveSimplex.firstFace.toOrderHom i, 4)) :=
  post_families_match (BassOverlap.commonReference P u v) (targetPost P v (underToLaurentInvert R))
    (CoefficientSquareFamilies.polynomialSource P u)
    (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map u)) (polynomialProjection P a))
    (moving_first_target_row P u v (underToLaurentInvert R) (laurentMinus_projection P c))
    (product_first_target_row P u v (underToLaurentInvert R) (laurentMinus_projection P b))
    2 (minus_target_corner P u v) i

/-- The full minus target centre, with concrete original node labels. -/
theorem minus_target_center :
    movingNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c) 5 =
    BassH1References.chartNodes P u v (underToLaurentInvert R) (laurentMinus_projection P b) 4 :=
  minus_first_target_nodes P u v 0

end Quillen.PerfectComplexes.BassMOuterJoin
