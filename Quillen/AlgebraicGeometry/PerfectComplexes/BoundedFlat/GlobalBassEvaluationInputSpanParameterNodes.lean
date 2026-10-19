/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputCommutingParameter
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputProjectionSquare
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputChartPrism

/-!
# The actual projection-square chart attachments

Each full eight-node projection square is postcomposed by its original raw chart map. Its
reference is fixed by the complete terminal node of the original strict-precomposed chart.
Both nodes on its evaluation side agree with the corresponding original prism column,
including their actual zero-preserving arrows and full reference isomorphisms.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputSpanParameterNodes
open GlobalSectionChangeIndex

attribute [local irreducible] evaluationComparisonIso evaluationCompositionTargetIso
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- All original nodes of the moving polynomial projection square. -/
def projectionNodes :=
  InputCommutingSimplex.nodes (polynomial.map g) (projection.app Y)
    (projection.app X) g (projection.naturality g)

/-- The unchanged projection-square reference before its actual raw chart postmap. -/
def projectionSource := InputCommutingSimplex.sourceMap (polynomial.map g) (projection.app Y)

/-- The complete terminal prism anchor at the actual attached projection arrow. -/
def terminalIso : (InputMixedDesc.sourceMap g).functor ≅
    ((projectionNodes g 6).1 ≫ evaluationRawMap (k.app X)).functor :=
  (InputChartReference.prismNode g k hk 2).2

/-- The prescribed reference is anchored at the original unconverted terminal chart node. -/
def sourceIso : (InputMixedDesc.sourceMap g).functor ≅
    (projectionSource g ≫ evaluationRawMap (k.app X)).functor :=
  terminalIso g k hk ≪≫
    isoWhiskerRight (projectionNodes g 6).2.symm (evaluationRawMap (k.app X)).functor

/-- Attach every full original projection node using its actual raw chart suffix. -/
def attachNode := CommonReferenceNerve.attachPostcompNode (projectionSource g)
  (evaluationRawMap (k.app X)) (InputMixedDesc.sourceMap g) (sourceIso g k hk)

/-- The eight original chart-postcomposed nodes in the fixed mixed Laurent reference. -/
def nodes (i : Fin 8) : CommonReferenceNerve.Node (InputMixedDesc.sourceMap g) :=
  attachNode g k hk (projectionNodes g i)

private theorem pinned_reference {V W T : Model.{u}} (F : V ⟶ W) (J : W ⟶ T)
    (R : V ⟶ T) (N : CommonReferenceNerve.Node F)
    (e : R.functor ≅ (N.1 ≫ J).functor) :
    (e ≪≫ isoWhiskerRight N.2.symm J.functor) ≪≫
      isoWhiskerRight N.2 J.functor = e := by
  rw [Iso.trans_assoc, ← isoWhiskerRight_trans, Iso.symm_self_id,
    isoWhiskerRight_refl]
  exact Iso.trans_refl e

/-- The initial evaluation-side node is the complete original unconverted prism endpoint. -/
theorem node_six : nodes g k hk 6 = InputChartReference.prismNode g k hk 2 := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  exact pinned_reference (projectionSource g) (evaluationRawMap (k.app X))
    (InputMixedDesc.sourceMap g) (projectionNodes g 6)
      (InputChartReference.prismNode g k hk 2).2

private theorem cut_target {A B C : Scheme.{u}} (f : A ⟶ B) (v : B ⟶ C) :
    (InputSimplex.anchors f v 3).symm ≪≫ InputSimplex.anchors f v 4 =
      evaluationCompositionSecondIso f v := by
  apply Iso.ext
  change (evaluationCompositionFirstIso f v).inv ≫
    ((evaluationComparisonIso (f ≫ v)).hom ≫ (evaluationCompositionTargetIso f v).hom) = _
  exact (congrArg (fun α => (evaluationCompositionFirstIso f v).inv ≫ α)
    (evaluationComposition_pasting f v)).trans
      (Iso.inv_hom_id_assoc (evaluationCompositionFirstIso f v)
        (evaluationCompositionSecondIso f v).hom)

private theorem cancel_prefix {C : Type*} [Category C] {A B D E : C}
    (e : A ≅ B) (f : B ≅ D) (h : B ≅ E) :
    (e ≪≫ f).symm ≪≫ (e ≪≫ h) = f.symm ≪≫ h := by
  simp only [Iso.trans_symm, Iso.trans_assoc, Iso.symm_self_id_assoc]

private theorem projection_cut_target :
    (projectionNodes g 6).2.symm ≪≫ (projectionNodes g 7).2 =
      evaluationCompositionSecondIso (projection.app X) g := by
  exact (cancel_prefix
    (InputCommutingSimplex.sourceIso (polynomial.map g) (projection.app Y)
      (projection.app X) g (projection.naturality g))
    (InputSimplex.anchors (projection.app X) g 3)
    (InputSimplex.anchors (projection.app X) g 4)).trans
      (cut_target (projection.app X) g)

private theorem post_reference {A B C : Type*} [Category A] [Category B] [Category C]
    {F G H : A ⥤ B} (J : B ⥤ C) {R : A ⥤ C}
    (e : R ≅ G ⋙ J) (a : F ≅ G) (b : F ≅ H) (η : G ≅ H)
    (h : a.symm ≪≫ b = η) :
    (e ≪≫ isoWhiskerRight a.symm J) ≪≫ isoWhiskerRight b J =
      e ≪≫ isoWhiskerRight η J := by
  rw [Iso.trans_assoc, ← isoWhiskerRight_trans, h]

private theorem whisker_twice {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    {F G : A ⥤ B} (e : F ≅ G) (J : B ⥤ C) (K : C ⥤ D) :
    isoWhiskerRight (isoWhiskerRight e J) K = isoWhiskerRight e (J ⋙ K) := rfl

private theorem normalization_two {A B C D : Scheme.{u}}
    (f : A ⟶ B) (v : B ⟶ C) (w : C ⟶ D) :
    InputNormalizationPrism.nodes f v w 2 = InputTripleNodes.preNode f v w 4 := rfl

private theorem normalization_five {A B C D : Scheme.{u}}
    (f : A ⟶ B) (v : B ⟶ C) (w : C ⟶ D) :
    InputNormalizationPrism.nodes f v w 5 = InputTripleNodes.preTargetNode f v w := rfl

private theorem trans_four {C : Type*} [Category C] {A B D E F : C}
    (a : A ≅ B) (b : B ≅ D) (c : D ≅ E) (d : E ≅ F) :
    (a ≪≫ b ≪≫ c) ≪≫ d = a ≪≫ b ≪≫ c ≪≫ d := by
  simp only [Iso.trans_assoc]

set_option backward.isDefEq.respectTransparency true in
private theorem prism_bridge :
    terminalIso g k hk ≪≫
      isoWhiskerRight (evaluationCompositionSecondIso (projection.app X) g)
        (evaluationRawMap (k.app X)).functor =
      (InputChartReference.prismNode g k hk 5).2 := by
  simp only [terminalIso, InputChartReference.prismNode, ModelSimplex.reanchorNodes,
    normalization_two, normalization_five, InputTripleNodes.preTargetNode,
    evaluationCompositionSecondIso, whisker_twice]
  exact trans_four (InputChartReference.chartSourceIso g k hk)
    (InputRectangleNodes.lastSourceIso (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g))
    (InputTripleNodes.preNode (k.app X) (projection.app X) g 4).2
    (isoWhiskerRight (evaluationComparisonIso g)
      ((evaluationRawMap (projection.app X)).functor ⋙ (evaluationRawMap (k.app X)).functor))

set_option backward.isDefEq.respectTransparency true in
private theorem attached_bridge :
    (nodes g k hk 7).2 = terminalIso g k hk ≪≫
      isoWhiskerRight (evaluationCompositionSecondIso (projection.app X) g)
        (evaluationRawMap (k.app X)).functor := by
  change (terminalIso g k hk ≪≫
    isoWhiskerRight (projectionNodes g 6).2.symm (evaluationRawMap (k.app X)).functor) ≪≫
    isoWhiskerRight (projectionNodes g 7).2 (evaluationRawMap (k.app X)).functor = _
  exact post_reference
    (F := (projectionSource g).functor)
    (G := (projectionNodes g 6).1.functor)
    (H := (projectionNodes g 7).1.functor)
    (R := (InputMixedDesc.sourceMap g).functor)
    (evaluationRawMap (k.app X)).functor
    (terminalIso g k hk)
    (projectionNodes g 6).2 (projectionNodes g 7).2
    (evaluationCompositionSecondIso (projection.app X) g) (projection_cut_target g)

set_option backward.isDefEq.respectTransparency true in
/-- The terminal evaluation-side node retains the actual original evaluation bridge. -/
theorem node_seven : nodes g k hk 7 = InputChartReference.prismNode g k hk 5 := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  exact (attached_bridge g k hk).trans (prism_bridge g k hk)


/-- The exact original commuting square remains the compact chart parameter. -/
def parameter :=
  (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (nodes g k hk)).comp
    InputCommutingParameter.parameter

/-- The entire finite diagram is unchanged by its actual chart attachment. -/
theorem simplex_eq :
    ModelSimplex.ofIsos (InputMixedDesc.sourceMap g)
      (fun i => (nodes g k hk i).1) (fun i => (nodes g k hk i).2) =
    (InputCommutingSimplex.simplex (polynomial.map g) (projection.app Y)
      (projection.app X) g (projection.naturality g)).postcomp
        (evaluationRawMap (k.app X)) := by
  change ModelSimplex.reanchorSimplex (sourceIso g k hk)
    (fun i => CommonReferenceNerve.postcompNode (evaluationRawMap (k.app X))
      (projectionNodes g i)) = _
  rw [ModelSimplex.reanchorSimplex_eq]
  exact (ModelSimplex.ofIsos_postcomp _ _ _ _).symm

/-- Every native coordinate is the original local projection square after the actual chart map. -/
theorem native (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (parameter g k hk) n =
    ((boundedFlatPerfectPrespectrumMap (k.app X)).map n).comp
      (((InputProjectionSquare.square g).level n).comp
        ⟨fun z => (z.1.1, (z.1.2, z.2)), by fun_prop⟩) := by
  apply ContinuousMap.ext
  rintro ⟨⟨r, s⟩, x⟩
  rw [CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ _
    (nodes g k hk) (r, s) (InputCommutingParameter.parameter (r, s)) rfl]
  rw [CommonReferenceNerve.prespectrumFamily_eq, simplex_eq,
    prespectrumSimplexFamily_postcomp]
  exact congrArg ((boundedFlatPerfectPrespectrumMap (k.app X)).map n)
    (InputCommutingParameter.native (polynomial.map g) (projection.app Y)
      (projection.app X) g (projection.naturality g) n r s x)

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputSpanParameterNodes
