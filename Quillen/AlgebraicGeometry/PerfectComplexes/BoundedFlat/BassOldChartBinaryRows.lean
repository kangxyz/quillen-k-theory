/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.RectangleInitialBinaryRow

/-! Exact outer and initial binary rows of the unchanged original composition charts. -/
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
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)

def oldOuterRowReference : (BassOverlap.commonReference P u v).functor ≅
    (BassOverlap.projectionMap P (a := a) ≫ BinaryNormalizationSimplex.sourceMap
      (BassReferenceMerge.laurentComposite P u v) (coefficientMap P (α.app a))).functor :=
  rectangleOuterReference
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map v))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
    (coefficientTransformation_naturality P α u).symm
    (coefficientTransformation_naturality P α v).symm
    (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
    (BassOverlap.commonToChartReference P u v α hc)

def oldInitialRowReference : (BassOverlap.commonReference P u v).functor ≅
    (BassOverlap.projectionMap P (a := a) ≫ BinaryNormalizationSimplex.sourceMap
      (coefficientMap P (α.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map v) ≫
        coefficientMap P ((polynomialUnderFunctor R).map u))).functor :=
  BassOverlap.commonToChartReference P u v α hc

/-- The original chart's entire outer binary row keeps its actual geometric transport. -/
theorem old_chart_outer_row (i : Fin 3) :
    BassOverlap.chartOverlapNodes P u v α hc (outerIndex i) =
      preBinaryNodes (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
        (BassReferenceMerge.laurentComposite P u v) (coefficientMap P (α.app a))
        (oldOuterRowReference P u v α hc) i :=
  rectangle_outer_row
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map v))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
    (coefficientTransformation_naturality P α u).symm
    (coefficientTransformation_naturality P α v).symm
    (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
    (BassOverlap.commonToChartReference P u v α hc) i

/-- The whole initial row uses the original two polynomial coefficient factors. -/
theorem old_chart_initial_row (i : Fin 3) :
    BassOverlap.chartOverlapNodes P u v α hc (initialIndex i) =
      preBinaryNodes (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
        (coefficientMap P (α.app c))
        (coefficientMap P ((polynomialUnderFunctor R).map v) ≫
          coefficientMap P ((polynomialUnderFunctor R).map u))
        (oldInitialRowReference P u v α hc) i :=
  rectangle_initial_row
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map v))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
    (coefficientTransformation_naturality P α u).symm
    (coefficientTransformation_naturality P α v).symm
    (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
    (BassOverlap.commonToChartReference P u v α hc) i

/-- Every old merged plus chart node retains its complete original reference. -/
theorem old_plus_node (i : Fin 18) :
    BassReferenceMerge.nodes P u v (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.plusFace.toOrderHom i)) =
      BassOverlap.chartOverlapNodes P u v (underToLaurent R) (laurentPlus_projection P c) i := by
  rw [BassReferenceMerge.chart_nodes]
  change BassBottomCommonFamily.nodes P u v (Fin.castAdd 15 (Fin.castAdd 18 i)) = _
  unfold BassBottomCommonFamily.nodes
  rw [Fin.addCases_left]
  unfold BassOverlap.nodes
  rw [Fin.addCases_left]

/-- The original plus chart's entire outer row survives the old dependent-node merge. -/
theorem old_plus_outer_row (i : Fin 3) :
    BassReferenceMerge.nodes P u v (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.plusFace.toOrderHom (outerIndex i))) =
    preBinaryNodes (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
      (BassReferenceMerge.laurentComposite P u v)
      (coefficientMap P ((underToLaurent R).app a))
      (oldOuterRowReference P u v (underToLaurent R) (laurentPlus_projection P c)) i := by
  rw [old_plus_node]
  exact old_chart_outer_row P u v (underToLaurent R) (laurentPlus_projection P c) i

/-- The original plus chart's entire initial row survives the old dependent-node merge. -/
theorem old_plus_initial_row (i : Fin 3) :
    BassReferenceMerge.nodes P u v (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.plusFace.toOrderHom (initialIndex i))) =
    preBinaryNodes (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
      (coefficientMap P ((underToLaurent R).app c))
      (coefficientMap P ((polynomialUnderFunctor R).map v) ≫
        coefficientMap P ((polynomialUnderFunctor R).map u))
      (oldInitialRowReference P u v (underToLaurent R) (laurentPlus_projection P c)) i := by
  rw [old_plus_node]
  exact old_chart_initial_row P u v (underToLaurent R) (laurentPlus_projection P c) i

/-- Every old merged minus chart node retains its complete original reference. -/
theorem old_minus_node (i : Fin 18) :
    BassReferenceMerge.nodes P u v (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.minusFace.toOrderHom i)) =
      BassOverlap.chartOverlapNodes P u v (underToLaurentInvert R)
        (laurentMinus_projection P c) i := by
  rw [BassReferenceMerge.chart_nodes]
  change BassBottomCommonFamily.nodes P u v (Fin.castAdd 15 (Fin.natAdd 18 i)) = _
  unfold BassBottomCommonFamily.nodes
  rw [Fin.addCases_left]
  unfold BassOverlap.nodes
  rw [Fin.addCases_right]

/-- The original minus chart's entire outer row survives the old dependent-node merge. -/
theorem old_minus_outer_row (i : Fin 3) :
    BassReferenceMerge.nodes P u v (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.minusFace.toOrderHom (outerIndex i))) =
    preBinaryNodes (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
      (BassReferenceMerge.laurentComposite P u v)
      (coefficientMap P ((underToLaurentInvert R).app a))
      (oldOuterRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P c)) i := by
  rw [old_minus_node]
  exact old_chart_outer_row P u v (underToLaurentInvert R) (laurentMinus_projection P c) i

/-- The original minus chart's entire initial row survives the old dependent-node merge. -/
theorem old_minus_initial_row (i : Fin 3) :
    BassReferenceMerge.nodes P u v (BassReferenceMerge.chartFace.toOrderHom
      (BassOverlap.minusFace.toOrderHom (initialIndex i))) =
    preBinaryNodes (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
      (coefficientMap P ((underToLaurentInvert R).app c))
      (coefficientMap P ((polynomialUnderFunctor R).map v) ≫
        coefficientMap P ((polynomialUnderFunctor R).map u))
      (oldInitialRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P c)) i := by
  rw [old_minus_node]
  exact old_chart_initial_row P u v (underToLaurentInvert R) (laurentMinus_projection P c) i

end Quillen.PerfectComplexes.BassH0Merge
