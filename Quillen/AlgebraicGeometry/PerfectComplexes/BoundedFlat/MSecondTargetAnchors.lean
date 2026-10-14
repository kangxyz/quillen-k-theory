/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MSecondTargetRows

/-! Full anchor nodes for the second and fourth original reassociation paths. -/
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

/-- The plus second-path corner is the actual shared first-path/product-row endpoint. -/
theorem plus_q_corner :
    movingNodes P u v (underToLaurent R) (laurentPlus_projection P c) 13 =
    h1MiddleChartNodes P u v (underToLaurent R) (laurentPlus_projection P b) 13 :=
  (plus_first_target_word_nodes P u v 4).trans
    (middle_product_chart_nodes P u v (underToLaurent R) (laurentPlus_projection P b) 4).symm

/-- Every complete first binary node of the plus second path keeps its full native reference. -/
theorem plus_q_first_nodes (i : Fin 3) :
    movingNodes P u v (underToLaurent R) (laurentPlus_projection P c)
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
    h1MiddleChartNodes P u v (underToLaurent R) (laurentPlus_projection P b)
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) :=
  prePost_families_match (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P u))
    (normalizedMap (coefficientMap P ((underToLaurent R).app c)))
    (CoefficientSquareFamilies.polynomialSource P v)
    (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map v)) (polynomialProjection P b))
    (moving_q_first_row P u v (underToLaurent R) (laurentPlus_projection P c))
    (old_q_first_row P u v (underToLaurent R) (laurentPlus_projection P b))
    2 (plus_q_corner P u v) i

/-- The full plus second-path centre with concrete unchanged original node labels. -/
theorem plus_q_center :
    movingNodes P u v (underToLaurent R) (laurentPlus_projection P c) 9 =
    h1MiddleChartNodes P u v (underToLaurent R) (laurentPlus_projection P b) 5 :=
  plus_q_first_nodes P u v 0

/-- The minus second-path corner is the actual shared first-path/product-row endpoint. -/
theorem minus_q_corner :
    movingNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c) 13 =
    h1MiddleChartNodes P u v (underToLaurentInvert R) (laurentMinus_projection P b) 13 :=
  (minus_first_target_word_nodes P u v 4).trans
    (middle_product_chart_nodes P u v (underToLaurentInvert R) (laurentMinus_projection P b) 4).symm

/-- Every complete first binary node of the minus second path keeps its full native reference. -/
theorem minus_q_first_nodes (i : Fin 3) :
    movingNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c)
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
    h1MiddleChartNodes P u v (underToLaurentInvert R) (laurentMinus_projection P b)
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) :=
  prePost_families_match (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P u))
    (normalizedMap (coefficientMap P ((underToLaurentInvert R).app c)))
    (CoefficientSquareFamilies.polynomialSource P v)
    (binaryNodes (coefficientMap P ((polynomialUnderFunctor R).map v)) (polynomialProjection P b))
    (moving_q_first_row P u v (underToLaurentInvert R) (laurentMinus_projection P c))
    (old_q_first_row P u v (underToLaurentInvert R) (laurentMinus_projection P b))
    2 (minus_q_corner P u v) i

/-- The full minus second-path centre with concrete unchanged original node labels. -/
theorem minus_q_center :
    movingNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c) 9 =
    h1MiddleChartNodes P u v (underToLaurentInvert R) (laurentMinus_projection P b) 5 :=
  minus_q_first_nodes P u v 0

end Quillen.PerfectComplexes.BassMOuterJoin
