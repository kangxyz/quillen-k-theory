/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H0ProjectionBoundaryRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetH0Reference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetCells

/-!
# The complete source row of the original target comparison

The initial H0 row is the unchanged five-node Bass projection path postcomposed with the
Laurent coefficient map. Its full reference is the original H0 binary normalization followed
by the actual projection equality. Both chart source transports remain explicit.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
open BassH0Merge BassH1Join CommonReferenceNerve CoefficientBassSeedTargetH0Reference

/-- Equality of the actual composite transports the entire original binary total. -/
theorem source_total_transport {A B C D : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (c : D ⟶ C) (r : C ⟶ A) (hr : q ≫ p = r) :
    eqToIso (ProjectionReference.anchor p q c r hr) ≪≫
        BinaryNormalizationSimplex.total c (q ≫ p) =
      BinaryNormalizationSimplex.total c r ≪≫
        isoWhiskerRight (eqToIso (congrArg (fun k ↦ (normalizedMap k).functor) hr.symm))
          (normalizedMap c).functor := by
  subst r
  simp only [eqToIso_refl, Iso.refl_trans, isoWhiskerRight_refl]
  exact (Iso.trans_refl (BinaryNormalizationSimplex.total c (q ≫ p))).symm

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
/-- The literal Laurent coefficient map at the target. -/
abbrev sourcePost := normalizedMap (coefficientMap P ((laurentUnderFunctor R).map f))

/-- The explicit source projection transport for either original chart. -/
def sourceChartIso (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a) :
    (normalizedMap (laurentProjection P a)).functor ≅
      (BinaryNormalizationSimplex.sourceMap (coefficientMap P (α.app a))
        (polynomialProjection P a)).functor :=
  eqToIso (congrArg (fun k ↦ (normalizedMap k).functor) ha.symm)

/-- The complete source-column anchor retains both its total and projection equality. -/
def sourceRowAnchor (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a) :
    (BassH0Diagram.reference P f).functor ≅
      (BinaryNormalizationSimplex.sourceMap (coefficientMap P (α.app a))
        (polynomialProjection P a) ≫ sourcePost P f).functor :=
  BinaryNormalizationSimplex.total
    (coefficientMap P ((laurentUnderFunctor R).map f)) (laurentProjection P a) ≪≫
      isoWhiskerRight (sourceChartIso P α ha) (sourcePost P f).functor

/-- All three full source nodes are the actual binary column with its normalized anchor. -/
theorem source_chart_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
    (i : Fin 3) :
    BassH0Diagram.chartNodes P f α ha (rectangleLeftIndex i) =
      postReferenceNode (BassH0Diagram.reference P f) (sourcePost P f) (sourceRowAnchor P f α ha)
        (binaryNodes (coefficientMap P (α.app a)) (polynomialProjection P a) i) := by
  rw [BassH1H0Boundary.chart_source_column]
  change (⟨_, (eqToIso (ProjectionReference.anchor _ _ _ _ ha) ≪≫
    BinaryNormalizationSimplex.total _ _) ≪≫ _⟩ : CommonReferenceNerve.Node _) = _
  rw [source_total_transport _ _ _ _ ha]
  rfl

/-- The positive anchor is exactly the public H0-to-source projection reference. -/
theorem plus_source_anchor :
    sourceRowAnchor P f (underToLaurent R) (laurentPlus_projection P a) =
      h0ProjectionIso P f := rfl

/-- The inverse source uses precisely the original positive-to-inverse source transport. -/
theorem minus_source_anchor :
    sourceRowAnchor P f (underToLaurentInvert R) (laurentMinus_projection P a) =
      h0ProjectionIso P f ≪≫
        isoWhiskerRight (BassProjectionPath.sourceIso P a) (sourcePost P f).functor := by
  have h : sourceChartIso P (underToLaurentInvert R) (laurentMinus_projection P a) =
      projectionReferenceIso P (a := a) ≪≫ BassProjectionPath.sourceIso P a := by
    apply Iso.ext
    simp only [sourceChartIso, projectionReferenceIso, BassProjectionPath.sourceIso,
      Iso.trans_hom, eqToIso.hom, eqToHom_trans]
  dsimp only [sourceRowAnchor, h0ProjectionIso, sourcePost,
    CoefficientBassSeedTargetChartAttachment.L]
  rw [h, isoWhiskerRight_trans, Iso.trans_assoc]

/-- The five source nodes retain the exact shared center and both separate intermediates. -/
def sourceRow : Fin 5 → Fin 31 := ![2, 3, 11, 14, 22]

/-- The complete initial H0 row equals the unchanged five-node Bass projection family. -/
theorem source_nodes (i : Fin 5) :
    BassH0Diagram.nodes P f (sourceRow i) =
      postReferenceNode (BassH0Diagram.reference P f) (sourcePost P f) (h0ProjectionIso P f)
        (BassProjectionPath.nodes P a i) := by
  fin_cases i
  · exact (BassH0Diagram.plus_nodes P f (rectangleLeftIndex 0)).trans
      ((source_chart_nodes P f (underToLaurent R) (laurentPlus_projection P a) 0).trans
        (by rw [plus_source_anchor]; rfl))
  · exact (BassH0Diagram.plus_nodes P f (rectangleLeftIndex 1)).trans
      ((source_chart_nodes P f (underToLaurent R) (laurentPlus_projection P a) 1).trans
        (by rw [plus_source_anchor]; rfl))
  · exact (BassH0Diagram.plus_nodes P f (rectangleLeftIndex 2)).trans
      ((source_chart_nodes P f (underToLaurent R) (laurentPlus_projection P a) 2).trans
        (by rw [plus_source_anchor]; rfl))
  · refine (BassH0Diagram.minus_nodes P f (rectangleLeftIndex 1)).trans
      ((source_chart_nodes P f (underToLaurentInvert R) (laurentMinus_projection P a) 1).trans ?_)
    rw [minus_source_anchor]
    exact (post_anchor_node (BassH0Diagram.reference P f) (sourcePost P f)
      (h0ProjectionIso P f) (BassProjectionPath.sourceIso P a)
      (binaryNodes (laurentMinus P a) (polynomialProjection P a) 1)).symm
  · refine (BassH0Diagram.minus_nodes P f (rectangleLeftIndex 2)).trans
      ((source_chart_nodes P f (underToLaurentInvert R) (laurentMinus_projection P a) 2).trans ?_)
    rw [minus_source_anchor]
    exact (post_anchor_node (BassH0Diagram.reference P f) (sourcePost P f)
      (h0ProjectionIso P f) (BassProjectionPath.sourceIso P a)
      (binaryNodes (laurentMinus P a) (polynomialProjection P a) 2)).symm

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
