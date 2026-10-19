/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputTripleNodes

/-!
# Full precomposed evaluation nodes in the original raw triple

Strict precomposition of the original evaluation chart retains its original source transport.
Appending the actual evaluation comparison along the final scheme map identifies three
complete dependent nodes with the right binary face of the original raw split triple.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputTripleNodes
open GlobalSectionChangeIndex
variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- The strict precomposition reference retains scheme association and original reindexing. -/
def preSourceIso : (sourceMap f g h).functor ≅
    (globalModel.map h.op ≫ InputSimplex.sourceMap f g).functor :=
  eqToIso (congrArg (fun k : X ⟶ T =>
    (globalModel.map k.op ≫ evaluationModel (op X)).functor) (Category.assoc f g h).symm) ≪≫
  eqToIso (congrArg (fun S => S ⋙ (evaluationModel (op X)).functor)
    (globalReindex_comp (f ≫ g) h)) ≪≫
  Functor.associator (globalModel.map h.op).functor
    (globalModel.map (f ≫ g).op).functor (evaluationModel (op X)).functor

/-- All five original evaluation-chart nodes after strict precomposition. -/
def preNode (i : Fin 5) : Node f g h :=
  ⟨globalModel.map h.op ≫ InputSimplex.vertices f g i,
    preSourceIso f g h ≪≫
      isoWhiskerLeft (globalModel.map h.op).functor (InputSimplex.anchors f g i)⟩

/-- The total node is converted by the actual final evaluation comparison. -/
def preTotalNode : Node f g h :=
  ⟨(evaluationModel (op T) ≫ evaluationRawMap h) ≫ evaluationRawMap (f ≫ g),
    (preNode f g h 1).2 ≪≫
      isoWhiskerRight (evaluationComparisonIso h) (evaluationRawMap (f ≫ g)).functor⟩

/-- The genuine binary intermediate is converted by the same actual evaluation comparison. -/
def preIntermediateNode : Node f g h :=
  ⟨(evaluationModel (op T) ≫ evaluationRawMap h) ≫
      BinaryNormalizationSimplex.intermediateMap f g,
    (preNode f g h 2).2 ≪≫ isoWhiskerRight (evaluationComparisonIso h)
      (BinaryNormalizationSimplex.intermediateMap f g).functor⟩

/-- The split target retains the original raw suffix in its final evaluation bridge. -/
def preTargetNode : Node f g h :=
  ⟨(evaluationModel (op T) ≫ evaluationRawMap h) ≫ (evaluationRawMap g ≫ evaluationRawMap f),
    (preNode f g h 4).2 ≪≫ isoWhiskerRight (evaluationComparisonIso h)
      (evaluationRawMap g ≫ evaluationRawMap f).functor⟩

private theorem comparison_transport {A B : Scheme.{u}} {a b : A ⟶ B} (e : a = b) :
    eqToHom (congrArg (fun k : A ⟶ B =>
      (globalModel.map k.op ≫ evaluationModel (op A)).functor) e) ≫
      (evaluationComparisonIso b).hom =
    (evaluationComparisonIso a).hom ≫
      whiskerLeft (evaluationModel (op B)).functor
        (eqToHom (congrArg (fun k : A ⟶ B => (evaluationRawMap k).functor) e)) := by
  subst b
  apply NatTrans.ext
  funext x
  change (𝟙 _ ≫ (evaluationComparisonIso a).hom.app x) =
    ((evaluationComparisonIso a).hom.app x ≫ 𝟙 _)
  rw [Category.id_comp, Category.comp_id]

private theorem right_reference : NormalizedTripleSimplex.rightFirst f g h =
    eqToIso (congrArg (fun k : X ⟶ T => (evaluationRawMap k).functor)
      (Category.assoc f g h).symm) ≪≫ evaluationRawCompIso (f ≫ g) h := by
  unfold NormalizedTripleSimplex.rightFirst evaluationRawCompIso
  exact whiskering_eqToIso_trans AsSmall.down AsSmall.up _ _

private theorem pre_first_anchor :
    (preSourceIso f g h).hom ≫
      (isoWhiskerLeft (globalModel.map h.op).functor (evaluationComparisonIso (f ≫ g))).hom =
    eqToHom (congrArg (fun k : X ⟶ T =>
      (globalModel.map k.op ≫ evaluationModel (op X)).functor) (Category.assoc f g h).symm) ≫
      (evaluationCompositionFirstIso (f ≫ g) h).hom := by
  apply NatTrans.ext
  funext x
  simp only [preSourceIso, evaluationCompositionFirstIso, Iso.trans_hom, Iso.symm_hom,
    eqToIso.hom, isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, comp_obj,
    Category.id_comp, Category.assoc]
  erw [Category.comp_id]

private theorem pre_total_anchor :
    ((preSourceIso f g h).hom ≫
      (isoWhiskerLeft (globalModel.map h.op).functor (evaluationComparisonIso (f ≫ g))).hom) ≫
      (isoWhiskerRight (evaluationComparisonIso h) (evaluationRawMap (f ≫ g)).functor).hom =
    (evaluationComparisonIso (f ≫ g ≫ h)).hom ≫
      (isoWhiskerLeft (evaluationModel (op T)).functor
        (NormalizedTripleSimplex.rightFirst f g h)).hom := by
  rw [pre_first_anchor, Category.assoc]
  change _ ≫ ((evaluationCompositionFirstIso (f ≫ g) h).hom ≫
    (evaluationCompositionSecondIso (f ≫ g) h).hom) = _
  rw [← evaluationComposition_pasting, ← Category.assoc,
    comparison_transport (Category.assoc f g h).symm]
  rw [right_reference]
  apply NatTrans.ext
  funext x
  simp only [evaluationCompositionTargetIso, Iso.trans_hom, Iso.symm_hom,
    isoWhiskerLeft_hom, NatTrans.comp_app, whiskerLeft_app, eqToIso.hom,
    Functor.associator_inv_app, Category.comp_id, Category.assoc]

/-- The full converted total node is the original right normalized triple node. -/
theorem pre_total_node : preTotalNode f g h = rawNode f g h 5 := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  exact pre_total_anchor f g h

private theorem pre_conversion_anchor
    (F : modelOf (boundedFlatPerfectWaldhausen Z) ⟶
      modelOf (boundedFlatPerfectWaldhausen X))
    (α : (evaluationRawMap (f ≫ g)).functor ≅ F.functor) :
    ((preSourceIso f g h).hom ≫
      (isoWhiskerLeft (globalModel.map h.op).functor
        (evaluationComparisonIso (f ≫ g) ≪≫
          isoWhiskerLeft (evaluationModel (op Z)).functor α)).hom) ≫
      (isoWhiskerRight (evaluationComparisonIso h) F.functor).hom =
    (((preSourceIso f g h).hom ≫
      (isoWhiskerLeft (globalModel.map h.op).functor (evaluationComparisonIso (f ≫ g))).hom) ≫
      (isoWhiskerRight (evaluationComparisonIso h) (evaluationRawMap (f ≫ g)).functor).hom) ≫
      (isoWhiskerLeft (evaluationModel (op T) ≫ evaluationRawMap h).functor α).hom := by
  apply NatTrans.ext
  funext x
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, Category.assoc]
  erw [← α.hom.naturality ((evaluationComparisonIso h).hom.app x)]

/-- The full converted intermediate node is the original right geometric split node. -/
theorem pre_intermediate_node : preIntermediateNode f g h = rawNode f g h 6 := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change (((preSourceIso f g h).hom ≫
    (isoWhiskerLeft (globalModel.map h.op).functor
      (evaluationComparisonIso (f ≫ g) ≪≫
        isoWhiskerLeft (evaluationModel (op Z)).functor
          (BinaryNormalizationSimplex.first f g))).hom) ≫
    (isoWhiskerRight (evaluationComparisonIso h)
      (BinaryNormalizationSimplex.intermediateMap f g).functor).hom) = _
  rw [pre_conversion_anchor, pre_total_anchor]
  apply NatTrans.ext
  funext x
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, NatTrans.comp_app,
    whiskerLeft_app, Category.assoc]
  rfl

/-- The full converted split target retains the raw triple's original left reference route. -/
theorem pre_target_node : preTargetNode f g h = rawNode f g h 7 := by
  apply ModelSimplex.reference_node_eq (by rfl)
  simp only [eqToHom_refl, Category.comp_id]
  change (((preSourceIso f g h).hom ≫
    (isoWhiskerLeft (globalModel.map h.op).functor
      (evaluationComparisonIso (f ≫ g) ≪≫ evaluationCompositionTargetIso f g)).hom) ≫
    (isoWhiskerRight (evaluationComparisonIso h)
      (evaluationRawMap g ≫ evaluationRawMap f).functor).hom) = _
  have hs : (evaluationCompositionTargetIso f g).hom =
      (isoWhiskerLeft (evaluationModel (op Z)).functor (evaluationRawCompIso f g)).hom := by
    apply NatTrans.ext
    funext x
    simp only [evaluationCompositionTargetIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.associator_inv_app, Category.comp_id]
  have hi : evaluationCompositionTargetIso f g =
      isoWhiskerLeft (evaluationModel (op Z)).functor (evaluationRawCompIso f g) := Iso.ext hs
  rw [hi]
  trans (((preSourceIso f g h).hom ≫
    (isoWhiskerLeft (globalModel.map h.op).functor (evaluationComparisonIso (f ≫ g))).hom) ≫
    (isoWhiskerRight (evaluationComparisonIso h) (evaluationRawMap (f ≫ g)).functor).hom) ≫
    (isoWhiskerLeft (evaluationModel (op T) ≫ evaluationRawMap h).functor
      (evaluationRawCompIso f g)).hom
  · exact pre_conversion_anchor f g h (evaluationRawMap g ≫ evaluationRawMap f)
      (evaluationRawCompIso f g)
  rw [pre_total_anchor]
  change ((evaluationComparisonIso (f ≫ g ≫ h)).hom ≫
    (isoWhiskerLeft (evaluationModel (op T)).functor
      (NormalizedTripleSimplex.rightFirst f g h)).hom) ≫ _ =
    (evaluationComparisonIso (f ≫ g ≫ h)).hom ≫
      (isoWhiskerLeft (evaluationModel (op T)).functor
        (NormalizedTripleSimplex.leftFirst f g h ≪≫
          NormalizedTripleSimplex.leftSecond f g h)).hom
  have hr := congrArg (whiskerLeft (evaluationModel (op T)).functor)
    (NormalizedTripleSimplex.two_routes f g h)
  rw [whiskerLeft_comp, whiskerLeft_comp] at hr
  simp only [Iso.trans_hom, isoWhiskerLeft_hom, whiskerLeft_comp, Category.assoc]
  rw [hr]
  rfl

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputTripleNodes
