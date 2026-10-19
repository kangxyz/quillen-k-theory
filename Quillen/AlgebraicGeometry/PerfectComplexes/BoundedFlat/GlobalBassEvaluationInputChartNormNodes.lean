/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputChartSquareParameter
public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputRawChartProductNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PreReferenceFamily

/-!
# Complete normalization rows of the chart square and evaluation product

The five normalization nodes of the original commuting chart square and the initial row of
its actual evaluation product are fixed precompositions of the same original raw square.
Both identities preserve the complete Model arrows and their full reference anchors,
including the equality transport in the second normalization route.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputChartNormalizationNodes
open GlobalSectionChangeIndex BassH0Merge

attribute [local irreducible] evaluationComparisonIso evaluationCompositionTargetIso

/-- The five original normalization nodes in their eight-node commuting square. -/
def normalizationRow : Fin 5 → Fin 8 := ![1, 2, 4, 5, 7]

private theorem node_anchor_congr {V W : Model.{u}} {F : V ⟶ W}
    {N M : CommonReferenceNerve.Node F} (e : N = M)
    (h : N.1.functor = M.1.functor) : N.2 ≪≫ eqToIso h = M.2 := by
  cases e
  simp

private theorem whisker_eqToIso {A B C : Type*}
    [Category A] [Category B] [Category C]
    (F : A ⥤ B) {G H : B ⥤ C} (e : G = H) :
    isoWhiskerLeft F (eqToIso e) = eqToIso (congrArg (fun K => F ⋙ K) e) := by
  cases e
  rfl

private theorem commuting_normalization_anchor {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
    (h : p ≫ v = q ≫ w) :
    evaluationComparisonIso (p ≫ v) ≪≫
        isoWhiskerLeft (evaluationModel (op C)).functor
          (NativeSquareFiveSimplex.sourceIso p v q w h) =
      InputCommutingSimplex.sourceIso p v q w h ≪≫ evaluationComparisonIso (q ≫ w) := by
  have he := node_anchor_congr (InputCommutingSimplex.secondNodes_one p v q w h).symm
    (congrArg (fun H => (evaluationModel (op C)).functor ⋙ H)
      (NativeSquareFiveSimplex.source_eq p v q w h))
  unfold NativeSquareFiveSimplex.sourceIso
  rw [whisker_eqToIso]
  exact he

private theorem commuting_normalization_node_0 {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
    (h : p ≫ v = q ≫ w) :
    InputCommutingSimplex.nodes p v q w h (normalizationRow 0) =
      preReferenceNode (InputCommutingSimplex.sourceMap p v) (evaluationModel (op C))
        (evaluationComparisonIso (p ≫ v)) (NativeSquareFiveSimplex.nodes p v q w h 0) := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change (evaluationComparisonIso (p ≫ v)).hom =
    (evaluationComparisonIso (p ≫ v) ≪≫ isoWhiskerLeft _ (Iso.refl _)).hom
  apply NatTrans.ext
  funext x
  exact (Category.comp_id _).symm

private theorem commuting_normalization_node_1 {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
    (h : p ≫ v = q ≫ w) :
    InputCommutingSimplex.nodes p v q w h (normalizationRow 1) =
      preReferenceNode (InputCommutingSimplex.sourceMap p v) (evaluationModel (op C))
        (evaluationComparisonIso (p ≫ v)) (NativeSquareFiveSimplex.nodes p v q w h 1) := by
  rfl

private theorem commuting_normalization_node_2 {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
    (h : p ≫ v = q ≫ w) :
    InputCommutingSimplex.nodes p v q w h (normalizationRow 2) =
      preReferenceNode (InputCommutingSimplex.sourceMap p v) (evaluationModel (op C))
        (evaluationComparisonIso (p ≫ v)) (NativeSquareFiveSimplex.nodes p v q w h 2) := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change (evaluationComparisonIso (p ≫ v) ≪≫ evaluationCompositionTargetIso p v).hom = _
  rw [InputNormalizationPrism.normalization_target]
  rfl

private theorem whiskered_reference_hom {V W T : Model.{u}}
    {F R : V ⟶ T} (E : V ⟶ W) {G H K : W ⟶ T}
    (ρ : F.functor ≅ (E ≫ G).functor) (σ : F.functor ≅ R.functor)
    (τ : R.functor ≅ (E ≫ H).functor) (η : G.functor ≅ H.functor)
    (δ : H.functor ≅ K.functor)
    (h : ρ ≪≫ isoWhiskerLeft E.functor η = σ ≪≫ τ) :
    (σ ≪≫ (τ ≪≫ isoWhiskerLeft E.functor δ)).hom =
      (ρ ≪≫ isoWhiskerLeft E.functor (η ≪≫ δ)).hom := by
  apply congrArg Iso.hom
  calc
    _ = (σ ≪≫ τ) ≪≫ isoWhiskerLeft E.functor δ := (Iso.trans_assoc _ _ _).symm
    _ = (ρ ≪≫ isoWhiskerLeft E.functor η) ≪≫ isoWhiskerLeft E.functor δ :=
      congrArg (fun e => e ≪≫ isoWhiskerLeft E.functor δ) h.symm
    _ = ρ ≪≫ (isoWhiskerLeft E.functor η ≪≫ isoWhiskerLeft E.functor δ) :=
      Iso.trans_assoc _ _ _
    _ = _ := congrArg (fun e => ρ ≪≫ e) (isoWhiskerLeft_trans E.functor η δ).symm

private theorem commuting_normalization_node_3 {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
    (h : p ≫ v = q ≫ w) :
    InputCommutingSimplex.nodes p v q w h (normalizationRow 3) =
      preReferenceNode (InputCommutingSimplex.sourceMap p v) (evaluationModel (op C))
        (evaluationComparisonIso (p ≫ v)) (NativeSquareFiveSimplex.nodes p v q w h 3) := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change (InputCommutingSimplex.sourceIso p v q w h ≪≫
    (evaluationComparisonIso (q ≫ w) ≪≫
      isoWhiskerLeft (evaluationModel (op C)).functor
        (BinaryNormalizationSimplex.first q w))).hom =
    (evaluationComparisonIso (p ≫ v) ≪≫
      isoWhiskerLeft (evaluationModel (op C)).functor
        (NativeSquareFiveSimplex.sourceIso p v q w h ≪≫
          BinaryNormalizationSimplex.first q w)).hom
  exact whiskered_reference_hom (evaluationModel (op C))
    (evaluationComparisonIso (p ≫ v)) (InputCommutingSimplex.sourceIso p v q w h)
    (evaluationComparisonIso (q ≫ w)) (NativeSquareFiveSimplex.sourceIso p v q w h)
    (BinaryNormalizationSimplex.first q w) (commuting_normalization_anchor p v q w h)

private theorem commuting_normalization_node_4 {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
    (h : p ≫ v = q ≫ w) :
    InputCommutingSimplex.nodes p v q w h (normalizationRow 4) =
      preReferenceNode (InputCommutingSimplex.sourceMap p v) (evaluationModel (op C))
        (evaluationComparisonIso (p ≫ v)) (NativeSquareFiveSimplex.nodes p v q w h 4) := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change (InputCommutingSimplex.sourceIso p v q w h ≪≫
    (evaluationComparisonIso (q ≫ w) ≪≫ evaluationCompositionTargetIso q w)).hom =
    (evaluationComparisonIso (p ≫ v) ≪≫
      isoWhiskerLeft (evaluationModel (op C)).functor
        (NativeSquareFiveSimplex.sourceIso p v q w h ≪≫
          BinaryNormalizationSimplex.total q w)).hom
  rw [InputNormalizationPrism.normalization_target]
  exact whiskered_reference_hom (evaluationModel (op C))
    (evaluationComparisonIso (p ≫ v)) (InputCommutingSimplex.sourceIso p v q w h)
    (evaluationComparisonIso (q ≫ w)) (NativeSquareFiveSimplex.sourceIso p v q w h)
    (BinaryNormalizationSimplex.total q w) (commuting_normalization_anchor p v q w h)

private theorem commuting_normalization_nodes {A B C D : Scheme.{u}}
    (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
    (h : p ≫ v = q ≫ w) (i : Fin 5) :
    InputCommutingSimplex.nodes p v q w h (normalizationRow i) =
      preReferenceNode (InputCommutingSimplex.sourceMap p v) (evaluationModel (op C))
        (evaluationComparisonIso (p ≫ v)) (NativeSquareFiveSimplex.nodes p v q w h i) := by
  fin_cases i
  · exact commuting_normalization_node_0 p v q w h
  · exact commuting_normalization_node_1 p v q w h
  · exact commuting_normalization_node_2 p v q w h
  · exact commuting_normalization_node_3 p v q w h
  · exact commuting_normalization_node_4 p v q w h

variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- The chart row retains its actual first normalization node as the complete anchor. -/
def chartAnchor : (InputMixedDesc.sourceMap g).functor ≅
    (InputNormalizationPrism.firstSource (projection.app Y) ≫
      InputRawChartRows.squareSource g k).functor :=
  (InputChartSquareParameter.nodes g k hk 1).2

/-- All five attached chart nodes are one complete precomposed original raw square family. -/
theorem chart_nodes (i : Fin 5) :
    InputChartSquareParameter.nodes g k hk (normalizationRow i) =
      preReferenceNode (InputMixedDesc.sourceMap g)
        (InputNormalizationPrism.firstSource (projection.app Y)) (chartAnchor g k hk)
        (InputRawChartRows.squareNodes g k i) := by
  unfold InputChartSquareParameter.nodes
  rw [commuting_normalization_nodes]
  exact BassH1Join.pre_pre_node (InputMixedDesc.sourceMap g)
    (globalModel.map (projection.app Y).op) (evaluationModel (op (polynomial.obj Y)))
    (InputRawChartRows.squareSource g k) (evaluationComparisonIso (laurent.map g ≫ k.app Y))
    (InputChartSquareParameter.sourceIso g k hk) (InputRawChartRows.squareNodes g k i)

private theorem pair_iso {V W T : Model.{u}} {F₀ F₁ : V ⟶ W} {G₀ G₁ : W ⟶ T}
    (e : F₀.functor ≅ F₁.functor) (d : G₀.functor ≅ G₁.functor) :
    (Functor.uncurry.obj (whiskeringLeft V W T)).mapIso (e.prod d) =
      isoWhiskerRight e G₀.functor ≪≫ isoWhiskerLeft F₁.functor d := by
  apply Iso.ext
  rfl

/-- Every initial product node retains the same raw square and the actual product anchor. -/
theorem product_nodes (i : Fin 5) :
    InputRawChartProductNodes.nodes g k hk (SimplexGrid.index 1 4 (0, i)) =
      preReferenceNode (InputMixedDesc.sourceMap g)
        (InputNormalizationPrism.firstSource (projection.app Y))
        (InputRawChartProductNodes.anchor g k hk) (InputRawChartRows.squareNodes g k i) := by
  unfold InputRawChartProductNodes.nodes CommonReferenceProduct.vertices
    CommonReferenceProduct.references
  rw [SimplexGrid.decode_index]
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change (InputRawChartProductNodes.anchor g k hk ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((Iso.refl _).prod (InputRawChartRows.squareNodes g k i).2)).hom = _
  erw [pair_iso
    (F₀ := InputNormalizationPrism.firstSource (projection.app Y))
    (F₁ := InputNormalizationPrism.firstSource (projection.app Y))
    (G₀ := InputRawChartRows.squareSource g k)
    (G₁ := (InputRawChartRows.squareNodes g k i).1)]
  simp only [isoWhiskerRight_refl, Iso.refl_trans]

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputChartNormalizationNodes
