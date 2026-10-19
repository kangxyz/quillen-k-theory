/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedInputUnit

/-! Full anchored corners of the original strict-unit times Laurent evaluation product. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedInputUnitNodes
open GlobalSectionChangeIndex InputNormalizationPrism CommonReferenceNerve
open InputSeedInputUnitProduct

private theorem pair_iso {V W T : Model.{u}} {F₀ F₁ : V ⟶ W} {G₀ G₁ : W ⟶ T}
    (e : F₀.functor ≅ F₁.functor) (d : G₀.functor ≅ G₁.functor) :
    (Functor.uncurry.obj (whiskeringLeft V W T)).mapIso (e.prod d) =
      isoWhiskerRight e G₀.functor ≪≫ isoWhiskerLeft F₁.functor d := by
  apply Iso.ext
  rfl

private theorem source_shift_node {V W T : Model.{u}} (R : V ⟶ T)
    (H : V ⟶ W) (G₀ G₁ : W ⟶ T) (η : R.functor ≅ (H ≫ G₀).functor)
    (ρ : G₀.functor ≅ G₁.functor) (α : H.functor ≅ H.functor)
    (τ : R.functor ≅ R.functor)
    (h : τ ≪≫ η = η ≪≫ isoWhiskerRight α G₀.functor) :
    (⟨H ≫ G₁, η ≪≫ (Functor.uncurry.obj (whiskeringLeft V W T)).mapIso
      (α.prod ρ)⟩ : Node R) =
    CommonReferenceProduct.reanchor τ
      ⟨H ≫ G₁, η ≪≫ (Functor.uncurry.obj (whiskeringLeft V W T)).mapIso
        ((Iso.refl _).prod ρ)⟩ := by
  apply congrArg (fun θ ↦ (⟨H ≫ G₁, θ⟩ : Node R))
  rw [pair_iso, pair_iso]
  simp only [isoWhiskerRight_refl, Iso.refl_trans]
  rw [← Iso.trans_assoc, ← h, Iso.trans_assoc]

private theorem identity_anchor_node {V W : Model.{u}} (F G : V ⟶ W)
    (h : F.functor = G.functor) :
    (⟨G, eqToIso h⟩ : Node F) = ⟨F, Iso.refl _⟩ := by
  apply ModelSimplex.reference_node_eq h.symm
  change eqToHom h ≫ eqToHom h.symm = 𝟙 _
  rw [eqToHom_trans, eqToHom_refl]

private theorem preserves_comp {V W T : Model.{u}} (F : V ⟶ W) (G : W ⟶ T)
    (α : 𝟭 V.category ≅ 𝟭 V.category) (β : 𝟭 W.category ≅ 𝟭 W.category)
    (γ : 𝟭 T.category ≅ 𝟭 T.category)
    (hF : Preserves F.functor α β) (hG : Preserves G.functor β γ) :
    Preserves (F ≫ G).functor α γ := fun A ↦
  (congrArg G.functor.map (hF A)).trans (hG (F.functor.obj A))

private theorem preserved_onFunctor {V W T : Model.{u}} (F : V ⟶ W) (G : W ⟶ T)
    (α : 𝟭 W.category ≅ 𝟭 W.category) (β : 𝟭 T.category ≅ 𝟭 T.category)
    (h : Preserves G.functor α β) :
    isoWhiskerRight (onFunctor F.functor α) G.functor = onFunctor (F ≫ G).functor β := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  exact h (F.functor.obj A)

private theorem eqToIso_associate {V W T U : Model.{u}} (R : V ⟶ U)
    (H : V ⟶ W) (F : W ⟶ T) (E : T ⟶ U)
    (h : R.functor = (H.functor ⋙ F.functor) ⋙ E.functor) :
    eqToIso (h.trans (Functor.assoc H.functor F.functor E.functor)) =
      eqToIso h ≪≫ Functor.associator H.functor F.functor E.functor :=
  (eqToIso_trans h (Functor.assoc H.functor F.functor E.functor)).symm

private theorem reassociate_node {V W T U : Model.{u}} (R : V ⟶ U)
    (H : V ⟶ W) (E : W ⟶ T) (D : T ⟶ U)
    (ρ : R.functor ≅ (H ≫ (E ≫ D)).functor)
    (τ : R.functor ≅ ((H ≫ E) ≫ D).functor)
    (h : ρ ≪≫ (Functor.associator H.functor E.functor D.functor).symm = τ) :
    (⟨H ≫ (E ≫ D), ρ⟩ : Node R) = ⟨(H ≫ E) ≫ D, τ⟩ := by
  apply ModelSimplex.reference_node_eq (Functor.assoc H.functor E.functor D.functor).symm
  exact congrArg Iso.hom h

private theorem original_anchor_word {V W T U K : Model.{u}} (R : V ⟶ U)
    (H : V ⟶ W) (F : W ⟶ T) (E : T ⟶ U) (E' : W ⟶ K) (D : K ⟶ U)
    (h : R.functor = (H.functor ⋙ F.functor) ⋙ E.functor)
    (e : (F ≫ E).functor ≅ (E' ≫ D).functor) :
    (eqToIso (h.trans (Functor.assoc H.functor F.functor E.functor)) ≪≫
      isoWhiskerLeft H.functor e) ≪≫
        (Functor.associator H.functor E'.functor D.functor).symm =
    eqToIso h ≪≫ Functor.associator H.functor F.functor E.functor ≪≫
      isoWhiskerLeft H.functor e ≪≫
        (Functor.associator H.functor E'.functor D.functor).symm := by
  refine (congrArg (fun a ↦ (a ≪≫ isoWhiskerLeft H.functor e) ≪≫
    (Functor.associator H.functor E'.functor D.functor).symm)
      (eqToIso_associate R H F E h)).trans ?_
  simp only [Iso.trans_assoc]

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

private theorem product_node (i j : Fin 2) :
    nodes g (Quillen.SimplexGrid.index 1 1 (i, j)) =
      (⟨unitMap Y ≫ firstVertices (laurent.map g) j, InputSeedInputUnitProduct.anchor g ≪≫
        (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
          ((unitAnchors Y i).prod (firstAnchors (laurent.map g) j))⟩ :
        Node (InputSeedCarrier.laurentRef g)) := by
  unfold InputSeedInputUnitProduct.nodes CommonReferenceProduct.vertices
    CommonReferenceProduct.references
  rw [Quillen.SimplexGrid.decode_index]
  rfl

set_option backward.isDefEq.respectTransparency true in
/-- The initial product corner is the original full mixed source, not only its native image. -/
theorem zero_node : nodes g 0 = InputSeedUnitNodes.lower g 0 := by
  change nodes g (Quillen.SimplexGrid.index 1 1 (0, 0)) = _
  rw [product_node]
  change (⟨unitMap Y ≫ firstSource (laurent.map g), InputSeedInputUnitProduct.anchor g ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((Iso.refl (unitMap Y).functor).prod
        (Iso.refl (firstSource (laurent.map g)).functor))⟩ :
      Node (InputSeedCarrier.laurentRef g)) = _
  rw [pair_iso, isoWhiskerRight_refl, isoWhiskerLeft_refl, Iso.refl_trans]
  refine (congrArg (fun e ↦ (⟨unitMap Y ≫ firstSource (laurent.map g), e⟩ :
    Node (InputSeedCarrier.laurentRef g)))
      (Iso.trans_refl (InputSeedInputUnitProduct.anchor g))).trans ?_
  exact identity_anchor_node (InputSeedCarrier.laurentRef g)
    (unitMap Y ≫ firstSource (laurent.map g)) (source_eq g)

set_option backward.isDefEq.respectTransparency true in
private theorem terminal_anchor :
    (InputSeedInputUnitProduct.anchor g ≪≫ isoWhiskerLeft (unitMap Y).functor
      (evaluationComparisonIso (laurent.map g))) ≪≫
      (Functor.associator (unitMap Y).functor (evaluationModel (op (laurent.obj Y))).functor
        (evaluationRawMap (laurent.map g)).functor).symm =
      evaluationCompositionFirstIso (laurent.map g) (GlobalRawBass.laurentProjection.app Y) :=
  original_anchor_word (InputSeedCarrier.laurentRef g) (unitMap Y)
    (globalModel.map (laurent.map g).op) (evaluationModel (op (laurent.obj X)))
    (evaluationModel (op (laurent.obj Y))) (evaluationRawMap (laurent.map g))
    (congrArg (fun F ↦ F ⋙ (evaluationModel (op (laurent.obj X))).functor)
      (globalReindex_comp (laurent.map g) (GlobalRawBass.laurentProjection.app Y)))
    (evaluationComparisonIso (laurent.map g))

set_option backward.isDefEq.respectTransparency true in
/-- The terminal lower corner retains the original Laurent evaluation reference word. -/
theorem one_node : nodes g 1 = InputSeedUnitNodes.lower g 3 := by
  change nodes g (Quillen.SimplexGrid.index 1 1 (0, 1)) = _
  rw [product_node]
  change (⟨unitMap Y ≫ firstTarget (laurent.map g), InputSeedInputUnitProduct.anchor g ≪≫
    (Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso
      ((Iso.refl (unitMap Y).functor).prod (evaluationComparisonIso (laurent.map g)))⟩ :
      Node (InputSeedCarrier.laurentRef g)) = _
  rw [pair_iso, isoWhiskerRight_refl, Iso.refl_trans]
  exact reassociate_node (InputSeedCarrier.laurentRef g) (unitMap Y)
    (evaluationModel (op (laurent.obj Y))) (evaluationRawMap (laurent.map g))
    (InputSeedInputUnitProduct.anchor g ≪≫
      isoWhiskerLeft (unitMap Y).functor (evaluationComparisonIso (laurent.map g)))
    (evaluationCompositionFirstIso (laurent.map g) (GlobalRawBass.laurentProjection.app Y))
    (terminal_anchor g)

/-- Actual strict Laurent reindexing and evaluation preserve the unchanged source unit. -/
theorem evaluation_preserves : Preserves (firstSource (laurent.map g)).functor
    (GlobalSchemeLaurentTrack.unit (op Y))
    (evaluationSmallUnit (op (laurent.obj X)) (GlobalSchemeLaurentTrack.laurentScalar (op X))) :=
  preserves_comp (globalModel.map (laurent.map g).op) (evaluationModel (op (laurent.obj X)))
    (GlobalSchemeLaurentTrack.unit (op Y)) (GlobalSchemeLaurentTrack.unit (op X))
    (evaluationSmallUnit (op (laurent.obj X)) (GlobalSchemeLaurentTrack.laurentScalar (op X)))
    (GlobalSchemeLaurentTrack.unit_naturality g.op)
    (evaluationModel_unit (op (laurent.obj X)) (GlobalSchemeLaurentTrack.laurentScalar (op X)))

set_option backward.isDefEq.respectTransparency true in
/-- The full original product reference intertwines the strict source unit. -/
theorem anchor_unit :
    InputSeedCarrier.commonUnit g ≪≫ InputSeedInputUnitProduct.anchor g =
      InputSeedInputUnitProduct.anchor g ≪≫
        isoWhiskerRight (unitIso Y) (firstSource (laurent.map g)).functor := by
  have h := preserved_onFunctor (unitMap Y) (firstSource (laurent.map g))
    (GlobalSchemeLaurentTrack.unit (op Y))
    (evaluationSmallUnit (op (laurent.obj X)) (GlobalSchemeLaurentTrack.laurentScalar (op X)))
    (evaluation_preserves g)
  exact (InputSeedCarrier.anchor_unit g
    ⟨unitMap Y ≫ firstSource (laurent.map g), InputSeedInputUnitProduct.anchor g⟩).trans
      (congrArg (fun e ↦ InputSeedInputUnitProduct.anchor g ≪≫ e) h.symm)

/-- Every shifted product node retains its actual common-unit anchor before realization. -/
theorem shifted_node (j : Fin 2) :
    nodes g (Quillen.SimplexGrid.index 1 1 (1, j)) =
      CommonReferenceProduct.reanchor (InputSeedCarrier.commonUnit g)
        (nodes g (Quillen.SimplexGrid.index 1 1 (0, j))) := by
  rw [product_node, product_node]
  exact source_shift_node (InputSeedCarrier.laurentRef g) (unitMap Y)
    (firstSource (laurent.map g)) (firstVertices (laurent.map g) j)
    (InputSeedInputUnitProduct.anchor g)
    (firstAnchors (laurent.map g) j) (unitIso Y) (InputSeedCarrier.commonUnit g) (anchor_unit g)

/-- The first shifted corner is the separately anchored original source. -/
theorem two_node : nodes g 2 = InputSeedUnitNodes.upper g 0 :=
  (shifted_node g 0).trans
    (congrArg (CommonReferenceProduct.reanchor (InputSeedCarrier.commonUnit g)) (zero_node g))

/-- The terminal shifted corner is the separately anchored original evaluation cut. -/
theorem three_node : nodes g 3 = InputSeedUnitNodes.upper g 3 :=
  (shifted_node g 1).trans
    (congrArg (CommonReferenceProduct.reanchor (InputSeedCarrier.commonUnit g)) (one_node g))

/-- The actual product order is unit first; the public square coordinates are evaluation first. -/
def cornerIndex : Fin 4 → Fin 16 := ![0, 3, 8, 11]

/-- Every product corner agrees as a complete dependent node in the main sixteen-node family. -/
theorem corners (i : Fin 4) : nodes g i = InputSeedUnitNodes.nodes g (cornerIndex i) := by
  fin_cases i
  · exact zero_node g
  · exact one_node g
  · exact two_node g
  · exact three_node g

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedInputUnitNodes
