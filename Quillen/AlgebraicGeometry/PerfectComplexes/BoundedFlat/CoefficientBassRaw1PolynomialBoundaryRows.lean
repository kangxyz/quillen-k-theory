/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1LaurentChartRestriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionRectangleSquareRows

/-!
# The original Laurent polynomial row on genuine polynomial chart inputs

The Laurent-level polynomial square is retained with its original naturality equality. Its
five complete nodes give the nonmonotone polynomial row of the original eighteen-node family.
The reference change from the projection source to the fixed first triple is explicit, even
for the reflexive projection equation. Precomposition by the actual source chart then gives
a family with genuine polynomial source. The whole original Ppath is identified using its
four ordered primitive edges, without extending that claim to the rectangle interior.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Convexity
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open scoped Simplicial Topology unitInterval
universe u

namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialBoundaryRows
open BassH0Merge BassH1Join CommonReferenceNerve
open CoefficientBassLaurentProjectionScalar

private theorem precomp_post_node {V W T U : Model.{u}} {F : V ⟶ T} {H : V ⟶ W}
    (A : U ⟶ V) (J : W ⟶ T) (ρ : F.functor ≅ (H ≫ J).functor)
    (N : CommonReferenceNerve.Node H) :
    precompNode A (postReferenceNode F J ρ N) =
      postReferenceNode (A ≫ F) J (isoWhiskerLeft A.functor ρ) (precompNode A N) := by
  have hf : (A ≫ (N.1 ≫ J)).functor = ((A ≫ N.1) ≫ J).functor := rfl
  apply Sigma.ext (Model.Hom.ext hf)
  apply heq_of_eq
  change isoWhiskerLeft A.functor (ρ ≪≫ isoWhiskerRight N.2 J.functor) =
    isoWhiskerLeft A.functor ρ ≪≫ isoWhiskerRight (isoWhiskerLeft A.functor N.2) J.functor
  rw [isoWhiskerLeft_trans, whisker_iso_interchange]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R) {a b : Under R} (f : a ⟶ b)

/-- The fixed first-triple reference of the original Laurent family. -/
abbrev laurentReference := CoefficientBassLaurentProjectionScalar.reference P α f

/-- The projection presentation uses the actual composite `q ≫ p`. -/
abbrev projectionReference := ProjectionReference.reference (cMap P f)
  (q P α (a := a) ≫ p P (a := a))

/-- The original first-reference transport is retained explicitly, although its equation is rfl. -/
def nativeFirstReference : (projectionReference P α f).functor ≅
    (laurentReference P α f).functor :=
  BassH1Join.nativeFirstReference (p P (a := a)) (q P α (a := a)) (cMap P f)
    (q P α (a := a) ≫ p P (a := a)) rfl

/-- All eighteen original nodes in the projection presentation. -/
abbrev projectionNodes := ProjectionReference.nodes (p P (a := a)) (q P α (a := a))
  (p' P (b := b)) (q' P α (b := b)) (aMap P f) (bMap P f) (cMap P f)
  (polynomial_square P f) (chart_square P α f) (q P α (a := a) ≫ p P (a := a)) rfl

/-- The projection presentation reanchors every full original node by the named transport. -/
theorem projection_nodes (i : Fin 18) :
    projectionNodes P α f i = anchorNode (nativeFirstReference P α f)
      (CoefficientBassLaurentProjectionScalar.nodes P α f i) := rfl

/-- Returning to the fixed first reference preserves the entire dependent node. -/
theorem projection_unanchor (i : Fin 18) :
    anchorNode (nativeFirstReference P α f).symm (projectionNodes P α f i) =
      CoefficientBassLaurentProjectionScalar.nodes P α f i := by
  rw [projection_nodes, anchorNode_assoc, Iso.symm_self_id]
  exact anchorNode_refl _

/-- The original Laurent-level polynomial square has Laurent source at `a`. -/
abbrev squareSource := NativeSquareFiveSimplex.source (bMap P f) (p P (a := a))

/-- Both raw normalization nodes and the original polynomial naturality cast are kept. -/
abbrev squareNodes := NativeSquareFiveSimplex.nodes (bMap P f) (p P (a := a))
  (p' P (b := b)) (aMap P f) (polynomial_square P f)

/-- The target chart is the actual Laurent image of `α` at `b`. -/
abbrev postMap := normalizedMap (q' P α (b := b))

/-- The complete polynomial anchor in the projection presentation. -/
abbrev projectionPolynomialAnchor := ProjectionRectangleSquareRows.polynomialAnchor
  (p P (a := a)) (q P α (a := a)) (q' P α (b := b)) (bMap P f) (cMap P f)
  (chart_square P α f) (q P α (a := a) ≫ p P (a := a)) rfl

/-- The complete anchor into the original fixed first-triple reference includes its reanchor. -/
def fixedPolynomialAnchor : (laurentReference P α f).functor ≅
    (squareSource P f ≫ postMap P α (b := b)).functor :=
  (nativeFirstReference P α f).symm ≪≫ projectionPolynomialAnchor P α f

/-- The complete five-node Laurent row retains the original square and its full reference. -/
theorem laurent_row_nodes (i : Fin 5) :
    CoefficientBassLaurentProjectionScalar.nodes P α f
      (ProjectionRectangleSquareRows.polynomialRow i) =
    postReferenceNode (laurentReference P α f) (postMap P α (b := b))
      (fixedPolynomialAnchor P α f) (squareNodes P f i) := by
  have h : projectionNodes P α f (ProjectionRectangleSquareRows.polynomialRow i) =
      postReferenceNode (projectionReference P α f) (postMap P α (b := b))
        (projectionPolynomialAnchor P α f) (squareNodes P f i) :=
    ProjectionRectangleSquareRows.polynomial_row_nodes
      (p P (a := a)) (q P α (a := a)) (p' P (b := b)) (q' P α (b := b))
      (aMap P f) (bMap P f) (cMap P f) (polynomial_square P f) (chart_square P α f)
      (q P α (a := a) ≫ p P (a := a)) rfl i
  rw [← projection_unanchor P α f, h]
  exact anchor_post_node _ _ _ _

/-- The exact Laurent Ppath uses only the four ordered primitive edges of its nonmonotone row. -/
theorem laurent_polynomial_parameter (t : I) :
    parameter (laurentReference P α f) (CoefficientBassLaurentProjectionScalar.nodes P α f)
      (StdSimplex.map ProjectionRectangleSquareRows.polynomialRow
        (NativeSquareFiveSimplex.parameter t)) =
    parameter (laurentReference P α f) (fun i ↦
      postReferenceNode (laurentReference P α f) (postMap P α (b := b))
        (fixedPolynomialAnchor P α f) (squareNodes P f i))
      (NativeSquareFiveSimplex.parameter t) := by
  have hs : parameter (projectionReference P α f) (projectionNodes P α f)
      (StdSimplex.map ProjectionRectangleSquareRows.polynomialRow
        (NativeSquareFiveSimplex.parameter t)) =
      parameter (projectionReference P α f) (fun i ↦
        postReferenceNode (projectionReference P α f) (postMap P α (b := b))
          (projectionPolynomialAnchor P α f) (squareNodes P f i))
        (NativeSquareFiveSimplex.parameter t) :=
    ProjectionRectangleSquareRows.polynomial_nerve_parameter
      (p P (a := a)) (q P α (a := a)) (p' P (b := b)) (q' P α (b := b))
      (aMap P f) (bMap P f) (cMap P f) (polynomial_square P f) (chart_square P α f)
      (q P α (a := a) ≫ p P (a := a)) rfl t
  have h := congrArg (mapParameter (anchorNode (nativeFirstReference P α f).symm)) hs
  rw [mapParameter_parameter, mapParameter_parameter] at h
  simpa only [projection_unanchor, anchor_post_node, fixedPolynomialAnchor] using h

variable (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)

/-- The fixed full eighteen-node reference after the actual source chart. -/
abbrev reference := CoefficientBassRaw1LaurentChartRestriction.chart P β (a := a) ≫
  laurentReference P α f

/-- The polynomial square is precomposed by the actual chart, giving Polynomial(a) source. -/
abbrev polynomialReference :=
  CoefficientBassRaw1LaurentChartRestriction.chart P β (a := a) ≫ squareSource P f

/-- The genuine polynomial-source square retains all five complete precomposed nodes. -/
def polynomialNodes : Fin 5 → CommonReferenceNerve.Node (polynomialReference P f β) :=
  fun i ↦ precompNode (CoefficientBassRaw1LaurentChartRestriction.chart P β (a := a))
    (squareNodes P f i)

/-- The complete anchor includes source-chart whiskering of the explicit first reanchor. -/
def polynomialAnchor : (reference P α f β).functor ≅
    (polynomialReference P f β ≫ postMap P α (b := b)).functor :=
  isoWhiskerLeft (CoefficientBassRaw1LaurentChartRestriction.chart P β (a := a)).functor
    ((nativeFirstReference P α f).symm ≪≫ projectionPolynomialAnchor P α f)

/-- Full-node postcomposition with the target chart and the entire fixed-reference anchor. -/
def rowNode (N : CommonReferenceNerve.Node (polynomialReference P f β)) :
    CommonReferenceNerve.Node (reference P α f β) :=
  postReferenceNode (reference P α f β) (postMap P α (b := b))
    (polynomialAnchor P α f β) N

/-- The complete actual five-node row after both original chart operations. -/
theorem row_nodes (i : Fin 5) :
    CoefficientBassRaw1LaurentChartRestriction.nodes P α β f
      (ProjectionRectangleSquareRows.polynomialRow i) =
      rowNode P α f β (polynomialNodes P f β i) := by
  change precompNode (CoefficientBassRaw1LaurentChartRestriction.chart P β (a := a))
    (CoefficientBassLaurentProjectionScalar.nodes P α f
      (ProjectionRectangleSquareRows.polynomialRow i)) = _
  rw [laurent_row_nodes]
  exact precomp_post_node _ _ _ _

/-- The whole original polynomial Ppath retains its unchanged reversed-first subdivision. -/
theorem row_parameter (t : I) :
    parameter (reference P α f β) (CoefficientBassRaw1LaurentChartRestriction.nodes P α β f)
      (ProjectionRectangleParameters.Ppath (𝟙 ⦋17⦌) t) =
    parameter (reference P α f β)
      (fun i ↦ rowNode P α f β (polynomialNodes P f β i))
      (NativeSquareFiveSimplex.parameter t) := by
  let ψ : CommonReferenceNerve.Node (laurentReference P α f) →
      CommonReferenceNerve.Node (reference P α f β) :=
    precompNode (CoefficientBassRaw1LaurentChartRestriction.chart P β (a := a))
  have hL := mapParameter_parameter ψ (CoefficientBassLaurentProjectionScalar.nodes P α f)
    (StdSimplex.map ProjectionRectangleSquareRows.polynomialRow
      (NativeSquareFiveSimplex.parameter t))
  have hR := mapParameter_parameter ψ (fun i ↦
    postReferenceNode (laurentReference P α f) (postMap P α (b := b))
      (fixedPolynomialAnchor P α f) (squareNodes P f i))
    (NativeSquareFiveSimplex.parameter t)
  have h := hL.symm.trans
    ((congrArg (mapParameter ψ) (laurent_polynomial_parameter P α f t)).trans hR)
  have hp : StdSimplex.map ProjectionRectangleSquareRows.polynomialRow
      (NativeSquareFiveSimplex.parameter t) =
      ProjectionRectangleParameters.Ppath (𝟙 ⦋17⦌) t :=
    ProjectionRectangleSquareRows.polynomial_parameter (𝟙 ⦋17⦌) t
  rw [hp] at h
  change parameter (reference P α f β)
    (fun i ↦ ψ (CoefficientBassLaurentProjectionScalar.nodes P α f i))
    (ProjectionRectangleParameters.Ppath (𝟙 ⦋17⦌) t) =
      parameter (reference P α f β)
        (fun i ↦ rowNode P α f β (polynomialNodes P f β i))
        (NativeSquareFiveSimplex.parameter t)
  refine h.trans ?_
  exact congrArg (fun M ↦ parameter (reference P α f β) M
    (NativeSquareFiveSimplex.parameter t))
    (funext (fun i ↦ (congrArg ψ (laurent_row_nodes P α f i)).symm.trans
      (row_nodes P α f β i)))

/-- The same complete Ppath is the image of the genuine polynomial-source square parameter. -/
theorem row_parameter_map (t : I) :
    parameter (reference P α f β) (CoefficientBassRaw1LaurentChartRestriction.nodes P α β f)
      (ProjectionRectangleParameters.Ppath (𝟙 ⦋17⦌) t) =
    mapParameter (rowNode P α f β)
      (parameter (polynomialReference P f β) (polynomialNodes P f β)
        (NativeSquareFiveSimplex.parameter t)) := by
  rw [mapParameter_parameter]
  exact row_parameter P α f β t

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialBoundaryRows
