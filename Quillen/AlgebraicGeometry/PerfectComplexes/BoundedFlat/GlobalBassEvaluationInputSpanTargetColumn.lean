/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSpanTargetNodes

/-!
# The actual terminal evaluation column of the span comparison

The two complete nodes of the original projection evaluation column agree with the terminal
raw-square product column. The original evaluation isomorphism cancels only after its complete
terminal anchored node has been identified.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputSpanTargetColumn
open GlobalSectionChangeIndex InputNormalizationPrism InputRawChartRows
private theorem pair_iso_other {V W T : Model.{u}} {F₀ F₁ : V ⟶ W} {G₀ G₁ : W ⟶ T}
    (e : F₀.functor ≅ F₁.functor) (d : G₀.functor ≅ G₁.functor) :
    (Functor.uncurry.obj (whiskeringLeft V W T)).mapIso (e.prod d) =
      isoWhiskerLeft F₀.functor d ≪≫ isoWhiskerRight e G₁.functor := by
  apply Iso.ext
  ext A
  exact d.hom.naturality (e.hom.app A)


private theorem product_node_index {V W T : Model.{u}} {p q : ℕ}
    (F₀ : V ⟶ W) (F : Fin (p + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.functor ≅ (F i).functor)
    (G₀ : W ⟶ T) (G : Fin (q + 1) → (W ⟶ T))
    (eta : ∀ i, G₀.functor ≅ (G i).functor) (R : V ⟶ T)
    (a : R.functor ≅ (F₀ ≫ G₀).functor) (i : Fin (p + 1)) (j : Fin (q + 1)) :
    (⟨CommonReferenceProduct.vertices F G (SimplexGrid.index p q (i, j)),
      a ≪≫ CommonReferenceProduct.references F₀ F ρ G₀ G eta
        (SimplexGrid.index p q (i, j))⟩ : CommonReferenceNerve.Node R) =
    ⟨F i ≫ G j, a ≪≫
      (Functor.uncurry.obj (whiskeringLeft V W T)).mapIso ((ρ i).prod (eta j))⟩ := by
  unfold CommonReferenceProduct.vertices CommonReferenceProduct.references
  rw [SimplexGrid.decode_index]


private theorem product_column_reference {V W T : Model.{u}}
    {F₀ F₁ : V ⟶ W} {G₀ G₁ : W ⟶ T} {R : V ⟶ T}
    (a : R.functor ≅ (F₀ ≫ G₀).functor)
    (e : F₀.functor ≅ F₁.functor) (d : G₀.functor ≅ G₁.functor) :
    (a ≪≫ (Functor.uncurry.obj (whiskeringLeft V W T)).mapIso
      ((Iso.refl F₀.functor).prod d)) ≪≫ isoWhiskerRight e G₁.functor =
    a ≪≫ (Functor.uncurry.obj (whiskeringLeft V W T)).mapIso (e.prod d) := by
  rw [pair_iso_other, pair_iso_other]
  simp only [isoWhiskerRight_refl, Iso.trans_refl, Iso.trans_assoc]


private theorem cancel_column {C : Type*} [Category C] {R A B : C}
    (a₀ b₀ : R ≅ A) (a₁ b₁ : R ≅ B) (e : A ≅ B)
    (hp : a₀ ≪≫ e = a₁) (hq : b₀ ≪≫ e = b₁) (ht : HEq a₁ b₁) :
    a₀.hom ≫ eqToHom (rfl : A = A) = b₀.hom := by
  rw [eqToHom_refl, Category.comp_id]
  apply (Iso.cancel_iso_hom_right _ _ e).mp
  exact (congrArg Iso.hom hp).trans
    ((congrArg Iso.hom (eq_of_heq ht)).trans (congrArg Iso.hom hq).symm)


private theorem cancel_terminal_nodes {V W : Model.{u}} {R : V ⟶ W}
    (N₀ M₀ N₁ M₁ : CommonReferenceNerve.Node R)
    (h₀ : N₀.1.functor = M₀.1.functor)
    (e : N₀.1.functor ≅ N₁.1.functor) (d : M₀.1.functor ≅ M₁.1.functor)
    (hp : N₀.2 ≪≫ e = N₁.2) (hq : M₀.2 ≪≫ d = M₁.2)
    (hed : HEq e d) (ht : N₁ = M₁) : N₀ = M₀ := by
  rcases N₀ with ⟨A, a⟩
  rcases M₀ with ⟨B, b⟩
  have hAB : A = B := Model.Hom.ext h₀
  subst B
  cases ht
  have hd : e = d := eq_of_heq hed
  subst d
  apply ModelSimplex.reference_node_eq rfl
  exact cancel_column a b N₁.2 N₁.2 e hp hq (HEq.rfl)


variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

private def columnAnchor (i : Fin 2) : (InputMixedDesc.sourceMap g).functor ≅
    (firstVertices (projection.app Y) i ≫
      BinaryNormalizationSimplex.targetMap (k.app X) (polynomial.map g)).functor :=
  InputRawChartProductNodes.anchor g k hk ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((firstAnchors (projection.app Y) i).prod (squareNodes g k 4).2)

private def columnNode (i : Fin 2) : InputChartReference.Node g :=
  ⟨firstVertices (projection.app Y) i ≫
    BinaryNormalizationSimplex.targetMap (k.app X) (polynomial.map g), columnAnchor g k hk i⟩

private theorem product_column_node (i : Fin 2) :
    InputRawChartProductNodes.nodes g k hk (SimplexGrid.index 1 4 (i, 4)) =
      columnNode g k hk i := by
  unfold InputRawChartProductNodes.nodes
  rw [product_node_index]
  rfl

set_option backward.isDefEq.respectTransparency true in
private theorem product_column_anchor :
    columnAnchor g k hk 0 ≪≫
      isoWhiskerRight (evaluationComparisonIso (projection.app Y))
        (BinaryNormalizationSimplex.targetMap (k.app X) (polynomial.map g)).functor =
      columnAnchor g k hk 1 := by
  dsimp only [columnAnchor, firstAnchors, Fin.cases_zero, Fin.cases_succ]
  exact product_column_reference (R := InputMixedDesc.sourceMap g)
    (F₀ := firstSource (projection.app Y)) (F₁ := firstTarget (projection.app Y))
    (G₀ := squareSource g k)
    (G₁ := BinaryNormalizationSimplex.targetMap (k.app X) (polynomial.map g))
    (InputRawChartProductNodes.anchor g k hk)
    (evaluationComparisonIso (projection.app Y)) (squareNodes g k 4).2

private theorem whisker_twice {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    {F G : A ⥤ B} (e : F ≅ G) (J : B ⥤ C) (K : C ⥤ D) :
    isoWhiskerRight (isoWhiskerRight e J) K = isoWhiskerRight e (J ⋙ K) := by
  apply Iso.ext
  ext x
  rfl

private theorem post_pasting {A B C : Type*} [Category A] [Category B] [Category C]
    {R : A ⥤ C} {F G H : A ⥤ B} (J : B ⥤ C)
    (a : R ≅ F ⋙ J) (e : F ≅ G) (d : G ≅ H) (b : F ≅ H) (h : e ≪≫ d = b) :
    (a ≪≫ isoWhiskerRight e J) ≪≫ isoWhiskerRight d J = a ≪≫ isoWhiskerRight b J := by
  rw [Iso.trans_assoc, ← isoWhiskerRight_trans, h]

private theorem first_target_iso {A B C : Scheme.{u}} (p : A ⟶ B) (v : B ⟶ C) :
    evaluationCompositionFirstIso p v ≪≫ evaluationCompositionSecondIso p v =
      evaluationComparisonIso (p ≫ v) ≪≫ evaluationCompositionTargetIso p v := by
  apply Iso.ext
  exact (evaluationComposition_pasting p v).symm

set_option backward.isDefEq.respectTransparency true in
private theorem span_column_anchor :
    (InputSpanParameterNodes.nodes g k hk 3).2 ≪≫
      isoWhiskerRight (evaluationComparisonIso (projection.app Y))
        (BinaryNormalizationSimplex.targetMap (k.app X) (polynomial.map g)).functor =
      (InputSpanParameterNodes.nodes g k hk 4).2 := by
  have hw := whisker_twice (evaluationComparisonIso (projection.app Y))
    (evaluationRawMap (polynomial.map g)).functor (evaluationRawMap (k.app X)).functor
  change (InputSpanParameterNodes.sourceIso g k hk ≪≫
      isoWhiskerRight (evaluationCompositionFirstIso (polynomial.map g) (projection.app Y))
        (evaluationRawMap (k.app X)).functor) ≪≫
      isoWhiskerRight (evaluationComparisonIso (projection.app Y))
        ((evaluationRawMap (polynomial.map g)).functor ⋙
          (evaluationRawMap (k.app X)).functor) =
    InputSpanParameterNodes.sourceIso g k hk ≪≫
      isoWhiskerRight (evaluationComparisonIso (polynomial.map g ≫ projection.app Y) ≪≫
        evaluationCompositionTargetIso (polynomial.map g) (projection.app Y))
        (evaluationRawMap (k.app X)).functor
  rw [← hw]
  exact post_pasting (evaluationRawMap (k.app X)).functor
    (InputSpanParameterNodes.sourceIso g k hk)
    (evaluationCompositionFirstIso (polynomial.map g) (projection.app Y))
    (evaluationCompositionSecondIso (polynomial.map g) (projection.app Y))
    (evaluationComparisonIso (polynomial.map g ≫ projection.app Y) ≪≫
      evaluationCompositionTargetIso (polynomial.map g) (projection.app Y))
    (first_target_iso (polynomial.map g) (projection.app Y))

private def spanEdge : (InputSpanParameterNodes.nodes g k hk 3).1.functor ≅
    (InputSpanParameterNodes.nodes g k hk 4).1.functor :=
  isoWhiskerRight (evaluationComparisonIso (projection.app Y))
    (BinaryNormalizationSimplex.targetMap (k.app X) (polynomial.map g)).functor

private def productEdge : (columnNode g k hk 0).1.functor ≅
    (columnNode g k hk 1).1.functor :=
  isoWhiskerRight (evaluationComparisonIso (projection.app Y))
    (BinaryNormalizationSimplex.targetMap (k.app X) (polynomial.map g)).functor

private theorem span_edge_anchor :
    (InputSpanParameterNodes.nodes g k hk 3).2 ≪≫ spanEdge g k hk =
      (InputSpanParameterNodes.nodes g k hk 4).2 := span_column_anchor g k hk

private theorem product_edge_anchor :
    (columnNode g k hk 0).2 ≪≫ productEdge g k hk = (columnNode g k hk 1).2 :=
  product_column_anchor g k hk

private theorem edges_heq : HEq (spanEdge g k hk) (productEdge g k hk) := HEq.rfl

attribute [local irreducible] spanEdge productEdge

attribute [local irreducible] columnAnchor evaluationComparisonIso evaluationCompositionTargetIso

set_option backward.isDefEq.respectTransparency true in
/-- The full original projection cut is the initial node of the actual terminal product column. -/
theorem column_initial_node :
    InputSpanParameterNodes.nodes g k hk 3 = InputRawChartProductNodes.nodes g k hk 4 := by
  change _ = InputRawChartProductNodes.nodes g k hk (SimplexGrid.index 1 4 (0, 4))
  rw [product_column_node]
  have he := (InputSpanTargetNodes.column_terminal_node g k hk).trans
    (product_column_node g k hk 1)
  exact cancel_terminal_nodes (R := InputMixedDesc.sourceMap g)
    (InputSpanParameterNodes.nodes g k hk 3) (columnNode g k hk 0)
    (InputSpanParameterNodes.nodes g k hk 4) (columnNode g k hk 1) rfl
    (spanEdge g k hk) (productEdge g k hk)
    (span_edge_anchor g k hk) (product_edge_anchor g k hk) (edges_heq g k hk) he




/-- The original cut-to-target edge of the projection diagram. -/
def projectionFace : ⦋1⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![3, 4], by decide⟩

/-- Both entire anchored column nodes agree with their original product vertices. -/
theorem column_nodes (i : Fin 2) :
    InputRawChartProductNodes.nodes g k hk ((SimplexGrid.columnFace 1 4 4).toOrderHom i) =
      InputSpanParameterNodes.nodes g k hk (projectionFace.toOrderHom i) := by
  fin_cases i
  · exact (column_initial_node g k hk).symm
  · exact (InputSpanTargetNodes.column_terminal_node g k hk).symm

private theorem map_edge_scalar {p q : ℕ} (a : ⦋p⦌ ⟶ ⦋q⦌)
    (i j : Fin (p + 1)) (t : unitInterval) :
    StdSimplex.map a.toOrderHom ((edge i j) t) =
      edge (a.toOrderHom i) (a.toOrderHom j) t := map_edge a i j t

/-- The whole terminal product column is the original projection evaluation edge. -/
theorem column_parameter (t : unitInterval) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputSpanParameterNodes.nodes g k hk) ((edge (k := 7) 3 4) t) =
        InputRawChartProductNodes.parameter g k hk (t, 1) := by
  change _ = CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
    (InputRawChartProductNodes.nodes g k hk) (InputRawSquareProduct.parameter (t, 1))
  rw [InputRawSquareProduct.parameter_square_one]
  have h := CommonReferenceNerve.parameter_eq_of_face_nodes (InputMixedDesc.sourceMap g)
    (InputSpanParameterNodes.nodes g k hk) (InputRawChartProductNodes.nodes g k hk)
    projectionFace (SimplexGrid.columnFace 1 4 4) (column_nodes g k hk)
    ((edge (k := 1) 0 1) t)
  have he : StdSimplex.map projectionFace.toOrderHom ((edge (k := 1) 0 1) t) =
      (edge (k := 7) 3 4) t := map_edge_scalar projectionFace 0 1 t
  exact (congrArg (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
    (InputSpanParameterNodes.nodes g k hk)) he).symm.trans h.symm

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputSpanTargetColumn
