/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MTargetMiddleRows

/-! Every full original projection-path node on the actual inter-stage M boundary. -/
@[expose] public section

open Quillen.PerfectComplexes.BassH0Merge
open Quillen.PerfectComplexes.BassH1Join
open Quillen.PerfectComplexes.BassMComponents
open Quillen.PerfectComplexes.BassMReferences


open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassMOuterJoin
open BassH0Merge BassH1Join BassMComponents BassMReferences
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The plus middle endpoint is the original second-path endpoint through the proved seam. -/
theorem target_middle_plus_endpoint :
    middleNodes P u v (Quillen.SimplexGrid.index 2 4 (2, 2)) =
    h1MiddleChartNodes P u v (underToLaurent R) (laurentPlus_projection P b) 17 :=
  (BassMJoin.plus_internal_nodes P u v 2).symm.trans
    (plus_second_target_word_nodes P u v 4)

/-- Every full plus projection node is shared with the unchanged H1 middle target. -/
theorem target_middle_plus_nodes (i : Fin 3) :
    middleNodes P u v (Quillen.SimplexGrid.index 2 4
      (2, Fin.castAdd 2 i)) =
    h1MiddleChartNodes P u v (underToLaurent R) (laurentPlus_projection P b)
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) :=
  pre_families_match (BassOverlap.commonReference P u v) (targetMiddlePre P u v)
    (BinaryNormalizationSimplex.sourceMap
      (coefficientMap P ((underToLaurent R).app c)) (polynomialProjection P c))
    (binaryNodes (coefficientMap P ((underToLaurent R).app c)) (polynomialProjection P c))
    (middle_target_plus_row P u v)
    (h1_target_projection_row P u v (underToLaurent R) (laurentPlus_projection P b))
    2 (target_middle_plus_endpoint P u v) i

/-- The actual H1 plus chart node retains its whole original middle-component reference. -/
theorem h1_middle_plus_nodes (i : Fin 18) :
    BassH1References.middleNodes P u v (BassH0Diagram.plusFace.toOrderHom i) =
    h1MiddleChartNodes P u v (underToLaurent R) (laurentPlus_projection P b) i :=
  congrArg (preReferenceNode (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P u)) (BassH1References.middleIso P u v))
    (BassH0Diagram.plus_nodes P v i)

/-- The minus middle endpoint is the original second-path endpoint through the proved seam. -/
theorem target_middle_minus_endpoint :
    middleNodes P u v (Quillen.SimplexGrid.index 2 4 (2, 4)) =
    h1MiddleChartNodes P u v (underToLaurentInvert R) (laurentMinus_projection P b) 17 :=
  (BassMJoin.minus_internal_nodes P u v 2).symm.trans
    (minus_second_target_word_nodes P u v 4)

/-- Every full minus projection node is shared with the unchanged H1 middle target. -/
theorem target_middle_minus_nodes (i : Fin 3) :
    middleNodes P u v (Quillen.SimplexGrid.index 2 4
      (2, BassProjectionPath.minusFace.toOrderHom i)) =
    h1MiddleChartNodes P u v (underToLaurentInvert R) (laurentMinus_projection P b)
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) :=
  pre_families_match (BassOverlap.commonReference P u v) (targetMiddlePre P u v)
    (BinaryNormalizationSimplex.sourceMap
      (coefficientMap P ((underToLaurentInvert R).app c)) (polynomialProjection P c))
    (binaryNodes (coefficientMap P ((underToLaurentInvert R).app c)) (polynomialProjection P c))
    (middle_target_minus_row P u v)
    (h1_target_projection_row P u v (underToLaurentInvert R) (laurentMinus_projection P b))
    2 (target_middle_minus_endpoint P u v) i

/-- The actual H1 minus chart node retains its whole original middle-component reference. -/
theorem h1_middle_minus_nodes (i : Fin 18) :
    BassH1References.middleNodes P u v (BassH0Diagram.minusFace.toOrderHom i) =
    h1MiddleChartNodes P u v (underToLaurentInvert R) (laurentMinus_projection P b) i :=
  congrArg (preReferenceNode (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P u)) (BassH1References.middleIso P u v))
    (BassH0Diagram.minus_nodes P v i)

/-- The entire five-node target projection path agrees as actual dependent nodes and references. -/
theorem target_middle_path_nodes (i : Fin 5) :
    middleNodes P u v (Quillen.SimplexGrid.index 2 4 (2, i)) =
    BassH1References.middleNodes P u v (firstMiddleFace.toOrderHom i) := by
  fin_cases i
  · exact (target_middle_plus_nodes P u v 0).trans (h1_middle_plus_nodes P u v 15).symm
  · exact (target_middle_plus_nodes P u v 1).trans (h1_middle_plus_nodes P u v 16).symm
  · exact (target_middle_plus_nodes P u v 2).trans (h1_middle_plus_nodes P u v 17).symm
  · exact (target_middle_minus_nodes P u v 1).trans (h1_middle_minus_nodes P u v 16).symm
  · exact (target_middle_minus_nodes P u v 2).trans (h1_middle_minus_nodes P u v 17).symm

end Quillen.PerfectComplexes.BassMOuterJoin
