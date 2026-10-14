/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionRightRows

/-! The four actual H0 chart-edge rows retain their complete original binary references. -/
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
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)

abbrev chartProjectionFirstRef := projectionFirstReference
  (polynomialProjection P a) (coefficientMap P (α.app a))
  (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v))) (laurentProjection P a) ha
  (BassOverlap.commonReference P u v) (reference_eq P u v)

abbrev chartProjectionMiddleRef := projectionMiddleReference
  (polynomialProjection P a) (coefficientMap P (α.app a)) (coefficientMap P (α.app c))
  (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
  (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
  (coefficientTransformation_naturality P α (u ≫ v)) (laurentProjection P a) ha
  (BassOverlap.commonReference P u v) (reference_eq P u v)

def chartFirstRowReference : (BassOverlap.commonReference P u v).functor ≅
    (BassOverlap.projectionMap P (a := a) ≫ BinaryNormalizationSimplex.sourceMap
      (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
      (coefficientMap P (α.app a))).functor :=
  rightRowReference (BassOverlap.commonReference P u v)
    (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
    (coefficientMap P (α.app a)) (polynomialProjection P a) (chartProjectionFirstRef P u v α ha)

def chartMiddleRowReference : (BassOverlap.commonReference P u v).functor ≅
    (BassOverlap.projectionMap P (a := a) ≫ BinaryNormalizationSimplex.sourceMap
      (coefficientMap P (α.app c))
      (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))).functor :=
  rightRowReference (BassOverlap.commonReference P u v) (coefficientMap P (α.app c))
    (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v))) (polynomialProjection P a)
    (chartProjectionMiddleRef P u v α ha)

/-- The exact first right row of the original single-arrow chart projection comparison. -/
theorem chart_first_row (i : Fin 3) :
    anchorNode (F₀ := BassOverlap.commonReference P u v)
      (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
      (BassH0Diagram.chartNodes P (u ≫ v) α ha
        (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))) =
    preBinaryNodes (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
      (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v))) (coefficientMap P (α.app a))
      (chartFirstRowReference P u v α ha) i :=
  projection_first_right_row
    (polynomialProjection P a) (coefficientMap P (α.app a))
    (polynomialProjection P c) (coefficientMap P (α.app c))
    (coefficientMap P (u ≫ v)) (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
    (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
    (coefficientTransformation_naturality P (polynomialUnderCoefficient R) (u ≫ v))
    (coefficientTransformation_naturality P α (u ≫ v)) (laurentProjection P a) ha
    (BassOverlap.commonReference P u v) (reference_eq P u v) i

/-- The exact middle right row retains the original chart naturality transport and raw node. -/
theorem chart_middle_row (i : Fin 3) :
    anchorNode (F₀ := BassOverlap.commonReference P u v)
      (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
      (BassH0Diagram.chartNodes P (u ≫ v) α ha
        (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))) =
    preBinaryNodes (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
      (coefficientMap P (α.app c)) (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
      (chartMiddleRowReference P u v α ha) i :=
  projection_middle_right_row
    (polynomialProjection P a) (coefficientMap P (α.app a))
    (polynomialProjection P c) (coefficientMap P (α.app c))
    (coefficientMap P (u ≫ v)) (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
    (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
    (coefficientTransformation_naturality P (polynomialUnderCoefficient R) (u ≫ v))
    (coefficientTransformation_naturality P α (u ≫ v)) (laurentProjection P a) ha
    (BassOverlap.commonReference P u v) (reference_eq P u v) i

/-- The complete original plus H0 first binary row in the common reference. -/
theorem plus_first_row (i : Fin 3) :
    nodes P u v (BassH0Diagram.plusFace.toOrderHom
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))) =
    preBinaryNodes (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
      (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
      (coefficientMap P ((underToLaurent R).app a))
      (chartFirstRowReference P u v (underToLaurent R) (laurentPlus_projection P a)) i := by
  have he := anchorNode_congr (F₀ := BassOverlap.commonReference P u v)
    (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
    (BassH0Diagram.plus_nodes P (u ≫ v)
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)))
  exact he.trans (chart_first_row P u v (underToLaurent R) (laurentPlus_projection P a) i)

/-- The complete original plus H0 middle binary row in the common reference. -/
theorem plus_middle_row (i : Fin 3) :
    nodes P u v (BassH0Diagram.plusFace.toOrderHom
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))) =
    preBinaryNodes (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
      (coefficientMap P ((underToLaurent R).app c))
      (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
      (chartMiddleRowReference P u v (underToLaurent R) (laurentPlus_projection P a)) i := by
  have he := anchorNode_congr (F₀ := BassOverlap.commonReference P u v)
    (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
    (BassH0Diagram.plus_nodes P (u ≫ v)
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)))
  exact he.trans (chart_middle_row P u v (underToLaurent R) (laurentPlus_projection P a) i)

/-- The complete original minus H0 first binary row in the common reference. -/
theorem minus_first_row (i : Fin 3) :
    nodes P u v (BassH0Diagram.minusFace.toOrderHom
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i))) =
    preBinaryNodes (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
      (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
      (coefficientMap P ((underToLaurentInvert R).app a))
      (chartFirstRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P a)) i := by
  have he := anchorNode_congr (F₀ := BassOverlap.commonReference P u v)
    (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
    (BassH0Diagram.minus_nodes P (u ≫ v)
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)))
  exact he.trans (chart_first_row P u v (underToLaurentInvert R) (laurentMinus_projection P a) i)

/-- The complete original minus H0 middle binary row in the common reference. -/
theorem minus_middle_row (i : Fin 3) :
    nodes P u v (BassH0Diagram.minusFace.toOrderHom
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i))) =
    preBinaryNodes (BassOverlap.commonReference P u v) (BassOverlap.projectionMap P (a := a))
      (coefficientMap P ((underToLaurentInvert R).app c))
      (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
      (chartMiddleRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P a)) i := by
  have he := anchorNode_congr (F₀ := BassOverlap.commonReference P u v)
    (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
    (BassH0Diagram.minus_nodes P (u ≫ v)
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)))
  exact he.trans (chart_middle_row P u v (underToLaurentInvert R) (laurentMinus_projection P a) i)

end Quillen.PerfectComplexes.BassH0Merge
