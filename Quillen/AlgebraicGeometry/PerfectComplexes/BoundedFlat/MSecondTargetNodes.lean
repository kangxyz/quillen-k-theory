/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MSecondTargetAnchors

/-! Complete full-node joins for the second and fourth original reassociation paths. -/
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

/-- The unchanged second target path is this original two-binary word. -/
def secondTargetWordIndex : Fin 5 → Fin 18 := ![9, 12, 13, 10, 11]

/-- All second binary nodes of the plus path retain their original reference transport. -/
theorem plus_q_second_nodes (i : Fin 3) :
    movingNodes P u v (underToLaurent R) (laurentPlus_projection P c)
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
    h1MiddleChartNodes P u v (underToLaurent R) (laurentPlus_projection P b)
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) :=
  prePost_families_match (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P u))
    (normalizedMap (coefficientMap P ((underToLaurent R).app c)))
    (BinaryNormalizationSimplex.sourceMap (polynomialProjection P c) (coefficientMap P v))
    (binaryNodes (polynomialProjection P c) (coefficientMap P v))
    (moving_q_second_row P u v (underToLaurent R) (laurentPlus_projection P c))
    (old_q_second_row P u v (underToLaurent R) (laurentPlus_projection P b))
    0 (plus_q_center P u v) i

/-- The whole plus second path agrees with the actual target path in H1's middle component. -/
theorem plus_second_target_word_nodes (i : Fin 5) :
    movingNodes P u v (underToLaurent R) (laurentPlus_projection P c)
      (secondTargetWordIndex i) =
    h1MiddleChartNodes P u v (underToLaurent R) (laurentPlus_projection P b)
      (polynomialWordIndex i) := by
  fin_cases i
  · exact plus_q_center P u v
  · exact plus_q_first_nodes P u v 1
  · exact plus_q_first_nodes P u v 2
  · exact plus_q_second_nodes P u v 1
  · exact plus_q_second_nodes P u v 2

/-- All second binary nodes of the minus path retain their original reference transport. -/
theorem minus_q_second_nodes (i : Fin 3) :
    movingNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c)
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
    h1MiddleChartNodes P u v (underToLaurentInvert R) (laurentMinus_projection P b)
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) :=
  prePost_families_match (BassOverlap.commonReference P u v)
    (normalizedMap (coefficientMap P u))
    (normalizedMap (coefficientMap P ((underToLaurentInvert R).app c)))
    (BinaryNormalizationSimplex.sourceMap (polynomialProjection P c) (coefficientMap P v))
    (binaryNodes (polynomialProjection P c) (coefficientMap P v))
    (moving_q_second_row P u v (underToLaurentInvert R) (laurentMinus_projection P c))
    (old_q_second_row P u v (underToLaurentInvert R) (laurentMinus_projection P b))
    0 (minus_q_center P u v) i

/-- The whole minus second path agrees with the actual target path in H1's middle component. -/
theorem minus_second_target_word_nodes (i : Fin 5) :
    movingNodes P u v (underToLaurentInvert R) (laurentMinus_projection P c)
      (secondTargetWordIndex i) =
    h1MiddleChartNodes P u v (underToLaurentInvert R) (laurentMinus_projection P b)
      (polynomialWordIndex i) := by
  fin_cases i
  · exact minus_q_center P u v
  · exact minus_q_first_nodes P u v 1
  · exact minus_q_first_nodes P u v 2
  · exact minus_q_second_nodes P u v 1
  · exact minus_q_second_nodes P u v 2

end Quillen.PerfectComplexes.BassMOuterJoin
