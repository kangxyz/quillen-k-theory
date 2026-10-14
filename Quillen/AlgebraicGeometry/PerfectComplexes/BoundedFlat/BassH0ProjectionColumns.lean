/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionLeftColumn

/-! Both exact H0 source binary columns, retaining their actual common-reference isomorphisms. -/
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

/-- The original chart projection equation composes with the actual H0 common-reference equality. -/
theorem chart_reference_eq (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a) :
    (BassOverlap.commonReference P u v).functor =
      (NormalizedTripleSimplex.sourceMap
        (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
        (coefficientMap P (α.app a)) (polynomialProjection P a)).functor :=
  (reference_eq P u v).trans
    (ProjectionReference.anchor (polynomialProjection P a) (coefficientMap P (α.app a))
      (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v))) (laurentProjection P a) ha)

/-- The complete positive source column uses its original postcomposed binary normalization. -/
theorem plus_source_column (i : Fin 3) :
    nodes P u v (BassH0Diagram.plusFace.toOrderHom (rectangleLeftIndex i)) =
      binaryColumnNode (BassOverlap.commonReference P u v)
        (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
        (laurentPlus P a) (polynomialProjection P a)
        (chart_reference_eq P u v (underToLaurent R) (laurentPlus_projection P a)) i := by
  have h := congrArg (fun N : BassH0Diagram.Node P (u ≫ v) ↦
      (⟨N.1, eqToIso (reference_eq P u v) ≪≫ N.2⟩ : BassOverlap.Node P u v))
    (BassH0Diagram.plus_nodes P (u ≫ v) (rectangleLeftIndex i))
  exact h.trans (projection_left_column
    (polynomialProjection P a) (laurentPlus P a)
    (polynomialProjection P c) (laurentPlus P c)
    (coefficientMap P (u ≫ v)) (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
    (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
    (coefficientTransformation_naturality P (polynomialUnderCoefficient R) (u ≫ v))
    (coefficientTransformation_naturality P (underToLaurent R) (u ≫ v))
    (laurentProjection P a) (laurentPlus_projection P a)
    (BassOverlap.commonReference P u v) (reference_eq P u v) i)

/-- The inverse source column retains the separate original inverse-chart binary normalization. -/
theorem minus_source_column (i : Fin 3) :
    nodes P u v (BassH0Diagram.minusFace.toOrderHom (rectangleLeftIndex i)) =
      binaryColumnNode (BassOverlap.commonReference P u v)
        (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
        (laurentMinus P a) (polynomialProjection P a)
        (chart_reference_eq P u v (underToLaurentInvert R) (laurentMinus_projection P a)) i := by
  have h := congrArg (fun N : BassH0Diagram.Node P (u ≫ v) ↦
      (⟨N.1, eqToIso (reference_eq P u v) ≪≫ N.2⟩ : BassOverlap.Node P u v))
    (BassH0Diagram.minus_nodes P (u ≫ v) (rectangleLeftIndex i))
  exact h.trans (projection_left_column
    (polynomialProjection P a) (laurentMinus P a)
    (polynomialProjection P c) (laurentMinus P c)
    (coefficientMap P (u ≫ v)) (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)))
    (coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)))
    (coefficientTransformation_naturality P (polynomialUnderCoefficient R) (u ≫ v))
    (coefficientTransformation_naturality P (underToLaurentInvert R) (u ≫ v))
    (laurentProjection P a) (laurentMinus_projection P a)
    (BassOverlap.commonReference P u v) (reference_eq P u v) i)

end Quillen.PerfectComplexes.BassH0Merge
