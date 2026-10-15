/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H0ProjectionBoundaryRows

/-! Whole original binary rows on the first/middle H1 join, with both fixed maps retained. -/
@[expose] public section

open Quillen.PerfectComplexes.BassH0Merge
open Quillen.PerfectComplexes.BassH1References


open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1Join
open BassH0Merge BassH1References
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The original first component's reference on its target binary row. -/
def firstRowReference (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a) :
    (BassOverlap.commonReference P u v).functor ≅
      (BassH1Components.coefficientMapModel P u ≫
        BinaryNormalizationSimplex.sourceMap (coefficientMap P (α.app b))
          (polynomialProjection P b) ≫ BassH1Components.laurentMap P v).functor :=
  firstIso P u v ≪≫ isoWhiskerRight (BassH1H0Boundary.targetRowReference P u α ha)
    (BassH1Components.laurentMap P v).functor

/-- The original middle component's reference on its source binary column. -/
def middleRowReference (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b) :
    (BassOverlap.commonReference P u v).functor ≅
      (BassH1Components.coefficientMapModel P u ≫
        BinaryNormalizationSimplex.sourceMap (coefficientMap P (α.app b))
          (polynomialProjection P b) ≫ BassH1Components.laurentMap P v).functor :=
  middleIso P u v ≪≫ isoWhiskerLeft (BassH1Components.coefficientMapModel P u).functor
    (eqToIso (BassH1H0Boundary.sourceAnchor P v α hb) ≪≫ BinaryNormalizationSimplex.total
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P (α.app b) ≫ polynomialProjection P b))

/-- The original plus target row of the first component, retaining both whiskerings. -/
theorem plus_first_row (i : Fin 3) :
    BassH1References.firstNodes P u v (BassH0Diagram.plusFace.toOrderHom
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))) =
    prePostNodes (BassOverlap.commonReference P u v)
      (BassH1Components.coefficientMapModel P u) (BassH1Components.laurentMap P v)
      (BinaryNormalizationSimplex.sourceMap
        (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
      (binaryNodes (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
      (firstRowReference P u v (underToLaurent R) (laurentPlus_projection P a)) i := by
  have hn := congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.laurentMap P v) (firstIso P u v))
    (BassH1H0Boundary.plus_target P u i)
  exact hn.trans (post_pre_node (BassOverlap.commonReference P u v)
    (BassH1Components.coefficientMapModel P u) (BassH1Components.laurentMap P v)
    (BinaryNormalizationSimplex.sourceMap
      (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
    (binaryNodes (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
    (BassH1H0Boundary.targetRowReference P u (underToLaurent R) (laurentPlus_projection P a))
    (firstIso P u v) i)

/-- The original plus source column of the middle component, with the same fixed maps. -/
theorem plus_middle_row (i : Fin 3) :
    BassH1References.middleNodes P u v
      (BassH0Diagram.plusFace.toOrderHom (rectangleLeftIndex i)) =
    prePostNodes (BassOverlap.commonReference P u v)
      (BassH1Components.coefficientMapModel P u) (BassH1Components.laurentMap P v)
      (BinaryNormalizationSimplex.sourceMap
        (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
      (binaryNodes (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
      (middleRowReference P u v (underToLaurent R) (laurentPlus_projection P b)) i := by
  have hn := congrArg (BassH0Merge.preReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.coefficientMapModel P u) (middleIso P u v))
    (BassH1H0Boundary.plus_source P v i)
  exact hn.trans (pre_post_node (BassOverlap.commonReference P u v)
    (BassH1Components.coefficientMapModel P u) (BassH1Components.laurentMap P v)
    (BinaryNormalizationSimplex.sourceMap
      (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
    (binaryNodes (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
    (eqToIso (BassH1H0Boundary.sourceAnchor P v (underToLaurent R) (laurentPlus_projection P b)) ≪≫
      BinaryNormalizationSimplex.total (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P ((underToLaurent R).app b) ≫ polynomialProjection P b))
    (middleIso P u v) i)

/-- The complete plus binary row is shared through its proved full central reference node. -/
theorem plus_middle_nodes (i : Fin 3) :
    BassH1References.firstNodes P u v (BassH0Diagram.plusFace.toOrderHom
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))) =
    BassH1References.middleNodes P u v
      (BassH0Diagram.plusFace.toOrderHom (rectangleLeftIndex i)) :=
  prePost_families_match (BassOverlap.commonReference P u v)
    (BassH1Components.coefficientMapModel P u) (BassH1Components.laurentMap P v)
    (BinaryNormalizationSimplex.sourceMap
      (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
    (binaryNodes (coefficientMap P ((underToLaurent R).app b)) (polynomialProjection P b))
    (plus_first_row P u v) (plus_middle_row P u v) 0 (first_middle_center P u v) i

/-- The original minus target row of the first component, retaining both whiskerings. -/
theorem minus_first_row (i : Fin 3) :
    BassH1References.firstNodes P u v (BassH0Diagram.minusFace.toOrderHom
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))) =
    prePostNodes (BassOverlap.commonReference P u v)
      (BassH1Components.coefficientMapModel P u) (BassH1Components.laurentMap P v)
      (BinaryNormalizationSimplex.sourceMap
        (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
      (binaryNodes (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
      (firstRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P a)) i := by
  have hn := congrArg (postReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.laurentMap P v) (firstIso P u v))
    (BassH1H0Boundary.minus_target P u i)
  exact hn.trans (post_pre_node (BassOverlap.commonReference P u v)
    (BassH1Components.coefficientMapModel P u) (BassH1Components.laurentMap P v)
    (BinaryNormalizationSimplex.sourceMap
      (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
    (binaryNodes (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
    (BassH1H0Boundary.targetRowReference P u (underToLaurentInvert R) (laurentMinus_projection P a))
    (firstIso P u v) i)

/-- The original minus source column of the middle component, with the same fixed maps. -/
theorem minus_middle_row (i : Fin 3) :
    BassH1References.middleNodes P u v
      (BassH0Diagram.minusFace.toOrderHom (rectangleLeftIndex i)) =
    prePostNodes (BassOverlap.commonReference P u v)
      (BassH1Components.coefficientMapModel P u) (BassH1Components.laurentMap P v)
      (BinaryNormalizationSimplex.sourceMap
        (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
      (binaryNodes (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
      (middleRowReference P u v (underToLaurentInvert R) (laurentMinus_projection P b)) i := by
  have hn := congrArg (BassH0Merge.preReferenceNode (BassOverlap.commonReference P u v)
    (BassH1Components.coefficientMapModel P u) (middleIso P u v))
    (BassH1H0Boundary.minus_source P v i)
  exact hn.trans (pre_post_node (BassOverlap.commonReference P u v)
    (BassH1Components.coefficientMapModel P u) (BassH1Components.laurentMap P v)
    (BinaryNormalizationSimplex.sourceMap
      (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
    (binaryNodes (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
    (eqToIso (BassH1H0Boundary.sourceAnchor P v (underToLaurentInvert R)
      (laurentMinus_projection P b)) ≪≫
      BinaryNormalizationSimplex.total (coefficientMap P ((laurentUnderFunctor R).map v))
        (coefficientMap P ((underToLaurentInvert R).app b) ≫ polynomialProjection P b))
    (middleIso P u v) i)

/-- The complete minus binary row is shared through its proved full central reference node. -/
theorem minus_middle_nodes (i : Fin 3) :
    BassH1References.firstNodes P u v (BassH0Diagram.minusFace.toOrderHom
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i))) =
    BassH1References.middleNodes P u v
      (BassH0Diagram.minusFace.toOrderHom (rectangleLeftIndex i)) :=
  prePost_families_match (BassOverlap.commonReference P u v)
    (BassH1Components.coefficientMapModel P u) (BassH1Components.laurentMap P v)
    (BinaryNormalizationSimplex.sourceMap
      (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
    (binaryNodes (coefficientMap P ((underToLaurentInvert R).app b)) (polynomialProjection P b))
    (minus_first_row P u v) (minus_middle_row P u v) 0 (first_middle_center P u v) i

end Quillen.PerfectComplexes.BassH1Join
