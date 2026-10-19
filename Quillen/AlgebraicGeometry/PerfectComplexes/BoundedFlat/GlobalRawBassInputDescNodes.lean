/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputChartRawFace
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionReferenceNodes

/-!
# The five complete shared nodes of the original raw input rectangles

Both original chart rectangles have the same outer-projection path, with vertex word
`2, 1, 0, 14, 15`. The full dependent nodes at these five indices agree in the fixed mixed
Laurent reference. Their original Model arrows and evaluation anchors are retained; the
other thirteen nodes of each chart remain separate.
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
namespace Quillen.PerfectComplexes.GlobalRawBass.InputDescNodes
open GlobalSectionChangeIndex GlobalBassEvaluation
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The actual outer-square vertices in either original eighteen-node rectangle. -/
def sharedIndex : Fin 5 → Fin 18 := ![0, 1, 2, 14, 15]

private def evaluateProjectionNode {A C D : Scheme.{u}} (c : D ⟶ C) (r : C ⟶ A)
    (N : ProjectionReference.Node c r) :
    Σ F : globalModel.obj (op A) ⟶ modelOf (boundedFlatPerfectWaldhausen D),
      (globalModel.map (c ≫ r).op ≫ evaluationModel (op D)).functor ≅ F.functor :=
  ⟨evaluationModel (op A) ≫ N.1,
    evaluationComparisonIso (c ≫ r) ≪≫
      isoWhiskerLeft (evaluationModel (op A)).functor N.2⟩

private def evaluateTripleNode {A B C D : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (c : D ⟶ C)
    (N : DoubleSquareCommonSimplex.Node p q c) : InputTripleNodes.Node c q p :=
  ⟨evaluationModel (op A) ≫ N.1,
    evaluationComparisonIso (c ≫ q ≫ p) ≪≫
      isoWhiskerLeft (evaluationModel (op A)).functor N.2⟩

/-- Evaluate a complete geometric outer-reference node with the original total comparison. -/
def evaluateNode (N : ProjectionReference.Node (laurent.map g) (laurentProjection.app Y)) :
    InputChartReference.Node g :=
  ⟨evaluationModel (op Y) ≫ N.1,
    evaluationComparisonIso (laurent.map g ≫ laurentProjection.app Y) ≪≫
      isoWhiskerLeft (evaluationModel (op Y)).functor N.2⟩

private theorem evaluation_transport {U V : Scheme.{u}} {f h : U ⟶ V} (e : f = h) :
    eqToIso (congrArg (fun j : U ⟶ V =>
      (globalModel.map j.op ≫ evaluationModel (op U)).functor) e) ≪≫
        evaluationComparisonIso h =
      evaluationComparisonIso f ≪≫
        isoWhiskerLeft (evaluationModel (op V)).functor
          (eqToIso (congrArg (fun j : U ⟶ V => (evaluationRawMap j).functor) e)) := by
  subst h
  apply Iso.ext
  ext x
  simp only [Iso.trans_hom, eqToIso.hom, eqToHom_refl, isoWhiskerLeft_hom,
    NatTrans.comp_app, whiskerLeft_app, NatTrans.id_app, Category.id_comp]
  exact (Category.comp_id _).symm

private theorem whisker_reanchor_node {U V W : Model.{u}}
    (J : U ⟶ V) (R₀ R₁ : V ⟶ W) (S₀ S₁ : U ⟶ W)
    (e : S₀.functor ≅ S₁.functor)
    (a₀ : S₀.functor ≅ (J ≫ R₀).functor)
    (a₁ : S₁.functor ≅ (J ≫ R₁).functor)
    (r : R₀.functor ≅ R₁.functor)
    (h : e ≪≫ a₁ = a₀ ≪≫ isoWhiskerLeft J.functor r)
    (N : Σ F : V ⟶ W, R₁.functor ≅ F.functor) :
    (⟨J ≫ N.1, e ≪≫ (a₁ ≪≫ isoWhiskerLeft J.functor N.2)⟩ :
      Σ F : U ⟶ W, S₀.functor ≅ F.functor) =
    ⟨J ≫ N.1, a₀ ≪≫ isoWhiskerLeft J.functor (r ≪≫ N.2)⟩ := by
  apply congrArg (fun a => (⟨J ≫ N.1, a⟩ : Σ F : U ⟶ W, S₀.functor ≅ F.functor))
  rw [isoWhiskerLeft_trans, ← Iso.trans_assoc, ← Iso.trans_assoc, h]

private theorem evaluate_reference_node {A B C D : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (c : D ⟶ C) (r : C ⟶ A) (hr : q ≫ p = r)
    (N : DoubleSquareCommonSimplex.Node p q c) :
    (⟨evaluationModel (op A) ≫ N.1,
      eqToIso (congrArg (fun j : D ⟶ A =>
        (globalModel.map j.op ≫ evaluationModel (op D)).functor)
          (congrArg (fun j => c ≫ j) hr).symm) ≪≫
        (evaluationComparisonIso (c ≫ q ≫ p) ≪≫
          isoWhiskerLeft (evaluationModel (op A)).functor N.2)⟩ :
      Σ F : globalModel.obj (op A) ⟶ modelOf (boundedFlatPerfectWaldhausen D),
        (globalModel.map (c ≫ r).op ≫ evaluationModel (op D)).functor ≅ F.functor) =
    ⟨evaluationModel (op A) ≫ N.1,
      evaluationComparisonIso (c ≫ r) ≪≫
        isoWhiskerLeft (evaluationModel (op A)).functor
          (eqToIso (ProjectionReference.anchor p q c r hr) ≪≫ N.2)⟩ :=
  whisker_reanchor_node (evaluationModel (op A))
    (ProjectionReference.reference c r) (NormalizedTripleSimplex.sourceMap c q p)
    (globalModel.map (c ≫ r).op ≫ evaluationModel (op D))
    (InputTripleNodes.sourceMap c q p)
    (eqToIso (congrArg (fun j : D ⟶ A =>
      (globalModel.map j.op ≫ evaluationModel (op D)).functor)
        (congrArg (fun j => c ≫ j) hr).symm))
    (evaluationComparisonIso (c ≫ r)) (evaluationComparisonIso (c ≫ q ≫ p))
    (eqToIso (ProjectionReference.anchor p q c r hr))
    (evaluation_transport (congrArg (fun j => c ≫ j) hr).symm) N

private theorem reanchor_refl_family {U V : Model.{u}} {F : U ⟶ V} {n : ℕ}
    (N : Fin (n + 1) → Σ G : U ⟶ V, F.functor ≅ G.functor) :
    ModelSimplex.reanchorNodes (Iso.refl F.functor) N = N := by
  funext i
  dsimp only [ModelSimplex.reanchorNodes]
  rw [Iso.refl_trans]

private theorem evaluate_reference_family {A B C D : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (c : D ⟶ C) (r : C ⟶ A) (hr : q ≫ p = r)
    {n : ℕ} (N : Fin (n + 1) → DoubleSquareCommonSimplex.Node p q c) :
    ModelSimplex.reanchorNodes
      (F₀ := globalModel.map (c ≫ r).op ≫ evaluationModel (op D))
      (F₁ := InputTripleNodes.sourceMap c q p)
      (eqToIso (congrArg (fun j : D ⟶ A =>
        (globalModel.map j.op ≫ evaluationModel (op D)).functor)
          (congrArg (fun j => c ≫ j) hr).symm))
      (fun i => evaluateTripleNode p q c (N i)) =
    fun i => evaluateProjectionNode c r
      (ModelSimplex.reanchorNodes
        (F₀ := ProjectionReference.reference c r)
        (F₁ := NormalizedTripleSimplex.sourceMap c q p)
        (eqToIso (ProjectionReference.anchor p q c r hr)) N i) := by
  subst r
  change ModelSimplex.reanchorNodes (Iso.refl (InputTripleNodes.sourceMap c q p).functor)
      (fun i => evaluateTripleNode p q c (N i)) =
    fun i => evaluateProjectionNode c (q ≫ p)
      (ModelSimplex.reanchorNodes
        (Iso.refl (NormalizedTripleSimplex.sourceMap c q p).functor) N i)
  rw [reanchor_refl_family]
  exact (congrArg
    (fun M : Fin (n + 1) → DoubleSquareCommonSimplex.Node p q c =>
      fun i => evaluateProjectionNode c (q ≫ p) (M i))
    (@reanchor_refl_family (modelOf (boundedFlatPerfectWaldhausen A))
      (modelOf (boundedFlatPerfectWaldhausen D))
      (NormalizedTripleSimplex.sourceMap c q p) n N)).symm

private theorem raw_rectangle_evaluated {A B C A' B' C' : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
    (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
    (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b) :
    InputRectangleNodes.rawNode p q p' q' a b c hp hq =
      fun i => evaluateTripleNode p q c
        (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq i) := rfl

private theorem projection_nodes_reanchored {A B C A' B' C' : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
    (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
    (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
    (r : C ⟶ A) (hr : q ≫ p = r) :
    ProjectionReference.nodes p q p' q' a b c hp hq r hr =
      ModelSimplex.reanchorNodes
        (F₀ := ProjectionReference.reference c r)
        (F₁ := NormalizedTripleSimplex.sourceMap c q p)
        (eqToIso (ProjectionReference.anchor p q c r hr))
        (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq) := rfl

private theorem raw_rectangle_family {A B C A' B' C' : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
    (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
    (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b)
    (r : C ⟶ A) (hr : q ≫ p = r) :
    ModelSimplex.reanchorNodes
      (F₀ := globalModel.map (c ≫ r).op ≫ evaluationModel (op C'))
      (F₁ := InputTripleNodes.sourceMap c q p)
      (eqToIso (congrArg (fun j : C' ⟶ A =>
        (globalModel.map j.op ≫ evaluationModel (op C')).functor)
          (congrArg (fun j => c ≫ j) hr).symm))
      (InputRectangleNodes.rawNode p q p' q' a b c hp hq) =
    fun i => evaluateProjectionNode c r
      (ProjectionReference.nodes p q p' q' a b c hp hq r hr i) := by
  rw [raw_rectangle_evaluated, projection_nodes_reanchored]
  exact evaluate_reference_family p q c r hr
    (DoubleSquareMergedSimplex.nodes p q p' q' a b c hp hq)

variable (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = laurentProjection.app Z)

/-- The complete original chart family is evaluated from its geometric projection family.
The reference change is exactly the actual chart projection equation. -/
theorem raw_node_evaluate_family :
    InputChartReference.rawNode g k hk =
      fun i => evaluateNode g
        (ProjectionReference.nodes (projection.app Y) (k.app Y)
          (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
          (projection.naturality g) (k.naturality g)
          (laurentProjection.app Y) (hk Y) i) := by
  exact raw_rectangle_family (projection.app Y) (k.app Y)
    (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
    (projection.naturality g) (k.naturality g) (laurentProjection.app Y) (hk Y)

/-- Every full original chart node keeps that same geometric evaluation transport. -/
theorem raw_node_evaluate (i : Fin 18) :
    InputChartReference.rawNode g k hk i =
      evaluateNode g
        (ProjectionReference.nodes (projection.app Y) (k.app Y)
          (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
          (projection.naturality g) (k.naturality g)
          (laurentProjection.app Y) (hk Y) i) :=
  congrFun (raw_node_evaluate_family g k hk) i

/-- The canonical common outer-square nodes, with the actual Laurent naturality anchor. -/
def outerNode (i : Fin 5) : InputChartReference.Node g :=
  evaluateNode g (ProjectionReference.outerNodes g (laurent.map g)
    (laurentProjection.app Y) (laurentProjection.app X)
    (laurentProjection.naturality g) i)

/-- All five complete chart nodes are the canonical common outer-square nodes. -/
theorem raw_shared_nodes (i : Fin 5) :
    InputChartReference.rawNode g k hk (sharedIndex i) = outerNode g i := by
  rw [raw_node_evaluate]
  exact congrArg (evaluateNode g)
    (ProjectionReference.shared_nodes (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g)
      (laurentProjection.app Y) (laurentProjection.app X) (hk Y) (hk X) i)

/-- Two actual chart factorizations share every full node of the entire outer path. -/
theorem shared_nodes (l : laurent ⟶ polynomial)
    (hl : ∀ Z, l.app Z ≫ projection.app Z = laurentProjection.app Z) (i : Fin 5) :
    InputChartReference.rawNode g k hk (sharedIndex i) =
      InputChartReference.rawNode g l hl (sharedIndex i) :=
  (raw_shared_nodes g k hk i).trans (raw_shared_nodes g l hl i).symm

/-- Both original raw Laurent charts share exactly these five outer-path nodes. -/
theorem plus_minus_shared_nodes (i : Fin 5) :
    InputChartReference.rawNode g plus plus_projection (sharedIndex i) =
      InputChartReference.rawNode g minus minus_projection (sharedIndex i) :=
  shared_nodes g plus plus_projection minus minus_projection i

/-- The total geometric source is shared with its complete mixed evaluation anchor. -/
theorem plus_minus_source_node :
    InputChartReference.rawNode g plus plus_projection 0 =
      InputChartReference.rawNode g minus minus_projection 0 :=
  plus_minus_shared_nodes g 0

/-- The source geometric normalization intermediate is a genuine shared outer node. -/
theorem plus_minus_source_intermediate_node :
    InputChartReference.rawNode g plus plus_projection 1 =
      InputChartReference.rawNode g minus minus_projection 1 :=
  plus_minus_shared_nodes g 1

/-- The source total endpoint of both chart paths is shared as a complete dependent node. -/
theorem plus_minus_source_total_node :
    InputChartReference.rawNode g plus plus_projection 2 =
      InputChartReference.rawNode g minus minus_projection 2 :=
  plus_minus_shared_nodes g 2

/-- The target geometric normalization intermediate keeps the same naturality anchor. -/
theorem plus_minus_target_intermediate_node :
    InputChartReference.rawNode g plus plus_projection 14 =
      InputChartReference.rawNode g minus minus_projection 14 :=
  plus_minus_shared_nodes g 3

/-- The target total endpoint is shared, retaining both original geometric square transports. -/
theorem plus_minus_target_total_node :
    InputChartReference.rawNode g plus plus_projection 15 =
      InputChartReference.rawNode g minus minus_projection 15 :=
  plus_minus_shared_nodes g 4

end Quillen.PerfectComplexes.GlobalRawBass.InputDescNodes
