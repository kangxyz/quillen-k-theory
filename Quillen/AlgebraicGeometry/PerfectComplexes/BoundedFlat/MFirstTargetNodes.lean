/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MFirstTargetAnchors

/-! Actual full joins for the first and last paths of the original reassociation boundary. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMOuterJoin
open BassH0Merge BassH1Join BassMComponents BassMReferences
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The first original target path has these unchanged two-binary labels. -/
def firstTargetWordIndex : Fin 5 → Fin 18 := ![5, 7, 17, 6, 13]

/-- The complete plus second target row retains its actual polynomial source transport. -/
theorem plus_second_target_nodes (i : Fin 3) :
    movingNodes P u v (underToLaurent R) (laurentPlus_projection P c)
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
    BassH1References.chartNodes P u v (underToLaurent R) (laurentPlus_projection P b)
      (Quillen.SimplexGrid.index 4 4 (NativeSquareFiveSimplex.secondFace.toOrderHom i, 4)) :=
  post_families_match (BassOverlap.commonReference P u v) (targetPost P v (underToLaurent R))
    (BinaryNormalizationSimplex.sourceMap (polynomialProjection P b) (coefficientMap P u))
    (binaryNodes (polynomialProjection P b) (coefficientMap P u))
    (moving_second_target_row P u v (underToLaurent R) (laurentPlus_projection P c))
    (product_second_target_row P u v (underToLaurent R) (laurentPlus_projection P b))
    0 (plus_target_center P u v) i

/-- Every node of the entire plus target path agrees with the fixed original product column. -/
theorem plus_first_target_word_nodes (i : Fin 5) :
    movingNodes P u v (underToLaurent R) (laurentPlus_projection P c) (firstTargetWordIndex i) =
    BassH1References.chartNodes P u v (underToLaurent R) (laurentPlus_projection P b)
      (Quillen.SimplexGrid.index 4 4 (i, 4)) := by
  fin_cases i
  · exact plus_first_target_nodes P u v 0
  · exact plus_first_target_nodes P u v 1
  · exact plus_first_target_nodes P u v 2
  · exact plus_second_target_nodes P u v 1
  · exact plus_second_target_nodes P u v 2

/-- The complete minus second target row retains its actual polynomial source transport. -/
theorem minus_second_target_nodes (i : Fin 3) :
    movingNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c)
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
    BassH1References.chartNodes P u v (underToLaurentInvert R) (laurentMinus_projection P b)
      (Quillen.SimplexGrid.index 4 4 (NativeSquareFiveSimplex.secondFace.toOrderHom i, 4)) :=
  post_families_match (BassOverlap.commonReference P u v) (targetPost P v (underToLaurentInvert R))
    (BinaryNormalizationSimplex.sourceMap (polynomialProjection P b) (coefficientMap P u))
    (binaryNodes (polynomialProjection P b) (coefficientMap P u))
    (moving_second_target_row P u v (underToLaurentInvert R) (laurentMinus_projection P c))
    (product_second_target_row P u v (underToLaurentInvert R) (laurentMinus_projection P b))
    0 (minus_target_center P u v) i

/-- Every node of the entire minus target path agrees with the fixed original product column. -/
theorem minus_first_target_word_nodes (i : Fin 5) :
    movingNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c)
      (firstTargetWordIndex i) =
    BassH1References.chartNodes P u v (underToLaurentInvert R) (laurentMinus_projection P b)
      (Quillen.SimplexGrid.index 4 4 (i, 4)) := by
  fin_cases i
  · exact minus_first_target_nodes P u v 0
  · exact minus_first_target_nodes P u v 1
  · exact minus_first_target_nodes P u v 2
  · exact minus_second_target_nodes P u v 1
  · exact minus_second_target_nodes P u v 2

end Quillen.PerfectComplexes.BassMOuterJoin
