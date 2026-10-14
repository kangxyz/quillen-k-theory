/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0BinaryRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassOldChartBinaryRows

/-! Four full H0/chart Laurent-row node identities from the original actual binary rows. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH0Merge
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The entire original plus Laurent row agrees through its already-proved full target. -/
theorem plus_laurent_rows (i : Fin 3) :
    nodes P u v (BassH0Diagram.plusFace.toOrderHom
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))) =
    BassReferenceMerge.nodes P u v (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.plusFace.toOrderHom (outerIndex i))) := by
  have ht := (plus_first_row P u v 2).symm.trans
    ((shared_positive_target_node P u v).trans (old_plus_outer_row P u v 2))
  have hr := preBinaryNodes_target_congr
    (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
    (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
    (coefficientMap P ((underToLaurent R).app a))
    (laurent_composite P u v) rfl
    (chartFirstRowReference P u v (underToLaurent R) (laurentPlus_projection P a))
    (oldOuterRowReference P u v (underToLaurent R) (laurentPlus_projection P c)) ht i
  exact (plus_first_row P u v i).trans (hr.trans (old_plus_outer_row P u v i).symm)

/-- The entire original minus Laurent row agrees through its already-proved full target. -/
theorem minus_laurent_rows (i : Fin 3) :
    nodes P u v (BassH0Diagram.minusFace.toOrderHom
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))) =
    BassReferenceMerge.nodes P u v (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.minusFace.toOrderHom (outerIndex i))) := by
  have ht := (minus_first_row P u v 2).symm.trans
    ((shared_negative_target_node P u v).trans (old_minus_outer_row P u v 2))
  have hr := preBinaryNodes_target_congr
    (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
    (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
    (coefficientMap P ((underToLaurentInvert R).app a))
    (laurent_composite P u v) rfl
    (chartFirstRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P a))
    (oldOuterRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P c)) ht i
  exact (minus_first_row P u v i).trans (hr.trans (old_minus_outer_row P u v i).symm)

/-- Full original shared node pair H0[9] = old[0], including its anchored reference. -/
theorem shared_positive_center_node : nodes P u v 9 = BassReferenceMerge.nodes P u v 0 :=
  plus_laurent_rows P u v 0

/-- Full original shared node pair H0[10] = old[14], including its anchored reference. -/
theorem shared_positive_laurent_raw_node : nodes P u v 10 = BassReferenceMerge.nodes P u v 14 :=
  plus_laurent_rows P u v 1

/-- Full original shared node pair H0[20] = old[24], including its anchored reference. -/
theorem shared_negative_center_node : nodes P u v 20 = BassReferenceMerge.nodes P u v 24 :=
  minus_laurent_rows P u v 0

/-- Full original shared node pair H0[21] = old[38], including its anchored reference. -/
theorem shared_negative_laurent_raw_node : nodes P u v 21 = BassReferenceMerge.nodes P u v 38 :=
  minus_laurent_rows P u v 1

end Quillen.PerfectComplexes.BassH0Merge
