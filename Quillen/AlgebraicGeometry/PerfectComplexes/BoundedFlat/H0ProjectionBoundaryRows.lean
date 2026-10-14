/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeProjectionBinaryRows

/-! Source and target binary rows of each original coefficient H0 projection diagram. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1H0Boundary
open BassH0Merge BassH1Join
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (w : a ⟶ b)
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)

abbrev sourceAnchor := ProjectionReference.anchor (polynomialProjection P a)
  (coefficientMap P (α.app a)) (coefficientMap P ((laurentUnderFunctor R).map w))
  (laurentProjection P a) ha

abbrev lastReference := nativeLastReference
  (polynomialProjection P a) (coefficientMap P (α.app a))
  (polynomialProjection P b) (coefficientMap P (α.app b))
  (coefficientMap P w) (coefficientMap P ((polynomialUnderFunctor R).map w))
  (coefficientMap P ((laurentUnderFunctor R).map w))
  (coefficientTransformation_naturality P (polynomialUnderCoefficient R) w)
  (coefficientTransformation_naturality P α w) (laurentProjection P a) ha

abbrev targetRowReference := rightRowReference (BassH0Diagram.reference P w)
  (coefficientMap P (α.app b)) (polynomialProjection P b) (coefficientMap P w)
  (lastReference P w α ha)

theorem chart_source_column (i : Fin 3) :
    BassH0Diagram.chartNodes P w α ha (rectangleLeftIndex i) =
      binaryColumnNode (BassH0Diagram.reference P w)
        (coefficientMap P ((laurentUnderFunctor R).map w))
        (coefficientMap P (α.app a)) (polynomialProjection P a) (sourceAnchor P w α ha) i :=
  native_source_column
    (polynomialProjection P a) (coefficientMap P (α.app a))
    (polynomialProjection P b) (coefficientMap P (α.app b))
    (coefficientMap P w) (coefficientMap P ((polynomialUnderFunctor R).map w))
    (coefficientMap P ((laurentUnderFunctor R).map w))
    (coefficientTransformation_naturality P (polynomialUnderCoefficient R) w)
    (coefficientTransformation_naturality P α w) (laurentProjection P a) ha i

theorem chart_target_row (i : Fin 3) :
    BassH0Diagram.chartNodes P w α ha
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) =
      preBinaryNodes (BassH0Diagram.reference P w) (normalizedMap (coefficientMap P w))
        (coefficientMap P (α.app b)) (polynomialProjection P b)
        (targetRowReference P w α ha) i :=
  native_target_row
    (polynomialProjection P a) (coefficientMap P (α.app a))
    (polynomialProjection P b) (coefficientMap P (α.app b))
    (coefficientMap P w) (coefficientMap P ((polynomialUnderFunctor R).map w))
    (coefficientMap P ((laurentUnderFunctor R).map w))
    (coefficientTransformation_naturality P (polynomialUnderCoefficient R) w)
    (coefficientTransformation_naturality P α w) (laurentProjection P a) ha i

/-- The full original plus source binary row retains its actual references. -/
theorem plus_source (i : Fin 3) :
    BassH0Diagram.nodes P w (BassH0Diagram.plusFace.toOrderHom (rectangleLeftIndex i)) =
      binaryColumnNode (BassH0Diagram.reference P w)
        (coefficientMap P ((laurentUnderFunctor R).map w))
        (coefficientMap P ((underToLaurent R).app a)) (polynomialProjection P a)
        (sourceAnchor P w (underToLaurent R) (laurentPlus_projection P a)) i :=
  (BassH0Diagram.plus_nodes P w (rectangleLeftIndex i)).trans
    (chart_source_column P w (underToLaurent R) (laurentPlus_projection P a) i)

/-- The full original plus target binary row retains its actual references. -/
theorem plus_target (i : Fin 3) :
    BassH0Diagram.nodes P w (BassH0Diagram.plusFace.toOrderHom
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))) =
      preBinaryNodes (BassH0Diagram.reference P w) (normalizedMap (coefficientMap P w))
        (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b)
        (targetRowReference P w (underToLaurent R) (laurentPlus_projection P a)) i :=
  (BassH0Diagram.plus_nodes P w
    (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))).trans
    (chart_target_row P w (underToLaurent R) (laurentPlus_projection P a) i)

/-- The full original minus source binary row retains its actual references. -/
theorem minus_source (i : Fin 3) :
    BassH0Diagram.nodes P w (BassH0Diagram.minusFace.toOrderHom (rectangleLeftIndex i)) =
      binaryColumnNode (BassH0Diagram.reference P w)
        (coefficientMap P ((laurentUnderFunctor R).map w))
        (coefficientMap P ((underToLaurentInvert R).app a)) (polynomialProjection P a)
        (sourceAnchor P w (underToLaurentInvert R) (laurentMinus_projection P a)) i :=
  (BassH0Diagram.minus_nodes P w (rectangleLeftIndex i)).trans
    (chart_source_column P w (underToLaurentInvert R) (laurentMinus_projection P a) i)

/-- The full original minus target binary row retains its actual references. -/
theorem minus_target (i : Fin 3) :
    BassH0Diagram.nodes P w (BassH0Diagram.minusFace.toOrderHom
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))) =
      preBinaryNodes (BassH0Diagram.reference P w) (normalizedMap (coefficientMap P w))
        (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b)
        (targetRowReference P w (underToLaurentInvert R) (laurentMinus_projection P a)) i :=
  (BassH0Diagram.minus_nodes P w
    (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))).trans
    (chart_target_row P w (underToLaurentInvert R) (laurentMinus_projection P a) i)

end Quillen.PerfectComplexes.BassH1H0Boundary
