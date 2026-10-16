/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Naturality

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassUnitBoundaryNodes
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionChartRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionFirstNormalNode
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionMiddleNormalNode

/-! Actual reference transport for the original H0 face at the identity coefficient arrow.
The geometric coefficient identities are applied to the existing projection rectangles;
all raw normalization vertices and both chart paths are retained. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.CoefficientBassUnitHZeroNodes
open OriginalUnitSquareSimplex CoefficientPolynomialSpanUnitNodes
open CoefficientBassUnitBoundaryNodes BassH0Merge BassH1Join

private theorem anchored_family {V W : Model.{u}} {F G : V ⟶ W} {k : ℕ}
    (ρ : F.functor ≅ G.functor) (N : Fin (k + 1) → Σ H : V ⟶ W, G.functor ≅ H.functor) :
    ModelSimplex.ofIsos F (fun i ↦ (anchorNode ρ (N i)).1)
        (fun i ↦ (anchorNode ρ (N i)).2) =
      ModelSimplex.ofIsos G (fun i ↦ (N i).1) (fun i ↦ (N i).2) :=
  ModelSimplex.ofIsos_change_reference ρ _ _

private theorem postReferenceNode_source {V W T : Model.{u}} (F : V ⟶ T)
    (J : W ⟶ T) {H : V ⟶ W} (ρ : F.functor ≅ (H ≫ J).functor) :
    postReferenceNode F J ρ ⟨H, Iso.refl _⟩ = ⟨H ≫ J, ρ⟩ := by
  unfold postReferenceNode
  dsimp only
  rw [isoWhiskerRight_refl]
  exact congrArg (fun η : F.functor ≅ (H ≫ J).functor ↦
    (⟨H ≫ J, η⟩ : Σ G : V ⟶ T, F.functor ≅ G.functor)) (Iso.trans_refl ρ)

private theorem post_identity_anchor {V W T : Model.{u}} (F : V ⟶ T)
    (H : V ⟶ W) (J : W ⟶ T) (ρ : F.functor ≅ (H ≫ J).functor)
    (N : Σ G : V ⟶ W, H.functor ≅ G.functor) :
    postReferenceNode F J (ρ ≪≫ isoWhiskerLeft H.functor (Iso.refl J.functor)) N =
      postReferenceNode F J ρ N := by
  rw [isoWhiskerLeft_refl]
  exact congrArg (fun σ ↦ postReferenceNode F J σ N) (Iso.trans_refl ρ)

private theorem pre_identity_anchor {V W T : Model.{u}} (F : V ⟶ T)
    (J : V ⟶ W) (H : W ⟶ T) (ρ : F.functor ≅ (J ≫ H).functor)
    (N : Σ G : W ⟶ T, H.functor ≅ G.functor) :
    preReferenceNode F J (ρ ≪≫ isoWhiskerRight (Iso.refl J.functor) H.functor) N =
      preReferenceNode F J ρ N := by
  rw [isoWhiskerRight_refl]
  exact congrArg (fun σ ↦ preReferenceNode F J σ N) (Iso.trans_refl ρ)

section UnitRows
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Actual scheme-unit transport into the first old binary comparison. -/
theorem rightBinarySourceEq : (sourceMap f).functor =
    (BinaryNormalizationSimplex.sourceMap (𝟙 X) f).functor :=
  congrArg (fun G ↦ AsSmall.down ⋙ G ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (Category.id_comp f).symm)

/-- Actual scheme-unit transport into the other old binary comparison. -/
theorem leftBinarySourceEq : (sourceMap f).functor =
    (BinaryNormalizationSimplex.sourceMap f (𝟙 Y)).functor :=
  congrArg (fun G ↦ AsSmall.down ⋙ G ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (Category.comp_id f).symm)

/-- The original first binary row, including its geometric normalization intermediate. -/
theorem unit_right_row (i : Fin 3) :
    (⟨vertices f (![0, 1, 2] i), references f (![0, 1, 2] i)⟩ :
      Σ G : modelOf (boundedFlatPerfectWaldhausen Y) ⟶
        modelOf (boundedFlatPerfectWaldhausen X), (sourceMap f).functor ≅ G.functor) =
      anchorNode (eqToIso (rightBinarySourceEq f)) (binaryNodes (𝟙 X) f i) := by
  fin_cases i
  · apply ModelSimplex.reference_node_eq (rightBinarySourceEq f)
    simp [references, binaryNodes]
  · apply ModelSimplex.reference_node_eq rfl
    simp only [eqToHom_refl, Category.comp_id]
    exact congrArg Iso.hom
      (whiskering_eqToIso_trans AsSmall.down AsSmall.up _ _)
  · apply ModelSimplex.reference_node_eq rfl
    simp only [eqToHom_refl, Category.comp_id]
    exact congrArg Iso.hom
      (whiskering_eqToIso_trans AsSmall.down AsSmall.up _ _)

/-- The second binary row keeps the other exact scheme-unit transport. -/
theorem unit_left_row (i : Fin 3) :
    (⟨vertices f (![0, 4, 5] i), references f (![0, 4, 5] i)⟩ :
      Σ G : modelOf (boundedFlatPerfectWaldhausen Y) ⟶
        modelOf (boundedFlatPerfectWaldhausen X), (sourceMap f).functor ≅ G.functor) =
      anchorNode (eqToIso (leftBinarySourceEq f)) (binaryNodes f (𝟙 Y) i) := by
  fin_cases i
  · apply ModelSimplex.reference_node_eq (leftBinarySourceEq f)
    simp [references, binaryNodes]
  · apply ModelSimplex.reference_node_eq rfl
    simp only [eqToHom_refl, Category.comp_id]
    exact congrArg Iso.hom
      (whiskering_eqToIso_trans AsSmall.down AsSmall.up _ _)
  · apply ModelSimplex.reference_node_eq rfl
    simp only [eqToHom_refl, Category.comp_id]
    exact congrArg Iso.hom
      (whiskering_eqToIso_trans AsSmall.down AsSmall.up _ _)
end UnitRows

private theorem anchor_pre_node {V W T : Model.{u}} {F K : V ⟶ T} (J : V ⟶ W)
    {H : W ⟶ T} (η : F.functor ≅ K.functor) (ρ : K.functor ≅ (J ≫ H).functor)
    (N : Σ G : W ⟶ T, H.functor ≅ G.functor) :
    anchorNode η (preReferenceNode K J ρ N) =
      preReferenceNode F J (η ≪≫ ρ) N := by
  rcases N with ⟨G, σ⟩
  apply ModelSimplex.reference_node_eq rfl
  simp only [eqToHom_refl, Category.comp_id, preReferenceNode, Iso.trans_hom,
    Category.assoc]

private theorem binary_target_transport {A B C : Scheme.{u}}
    (p p' : B ⟶ A) (q q' : C ⟶ B) (hp : p = p') (hq : q = q')
    (F : modelOf (boundedFlatPerfectWaldhausen A) ⟶ modelOf (boundedFlatPerfectWaldhausen C))
    (δ : F.functor ≅ (BinaryNormalizationSimplex.sourceMap q p).functor) :
    anchorNode (δ ≪≫ eqToIso (by subst p'; subst q'; rfl))
        (⟨BinaryNormalizationSimplex.targetMap q' p', BinaryNormalizationSimplex.total q' p'⟩ :
          Σ G : modelOf (boundedFlatPerfectWaldhausen A) ⟶
            modelOf (boundedFlatPerfectWaldhausen C),
            (BinaryNormalizationSimplex.sourceMap q' p').functor ≅ G.functor) =
      ⟨BinaryNormalizationSimplex.targetMap q p, δ ≪≫ BinaryNormalizationSimplex.total q p⟩ := by
  subst p'
  subst q'
  simp only [eqToIso_refl, Iso.trans_refl, anchorNode]

section Rectangle
variable {A B C : Scheme.{u}} (p : B ⟶ A) (q : C ⟶ B)
  (F : modelOf (boundedFlatPerfectWaldhausen A) ⟶ modelOf (boundedFlatPerfectWaldhausen C))
  (δ : F.functor ≅ (BinaryNormalizationSimplex.sourceMap q p).functor)

/-- The exact source equality of the unchanged identity projection rectangle. -/
theorem rectangleSourceEq : (BinaryNormalizationSimplex.sourceMap q p).functor =
    (ProjectionReference.reference (𝟙 C) (q ≫ p)).functor :=
  congrArg (fun G ↦ AsSmall.down ⋙ G ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (Category.id_comp (q ≫ p)).symm)

/-- The original identity rectangle, anchored only by the displayed native projection iso. -/
def rectangleNodes (i : Fin 18) :
    Σ G : modelOf (boundedFlatPerfectWaldhausen A) ⟶
      modelOf (boundedFlatPerfectWaldhausen C), F.functor ≅ G.functor :=
  anchorNode (δ ≪≫ eqToIso (rectangleSourceEq p q))
    (ProjectionReference.nodes p q p q (𝟙 A) (𝟙 B) (𝟙 C)
      (by simp) (by simp) (q ≫ p) rfl i)

/-- Its first normalized chart source retains the true binary total reference. -/
theorem rectangle_first_source : rectangleNodes p q F δ 9 =
    ⟨BinaryNormalizationSimplex.targetMap q p, δ ≪≫ BinaryNormalizationSimplex.total q p⟩ := by
  unfold rectangleNodes
  rw [projection_first_normal]
  change anchorNode (δ ≪≫ eqToIso (rectangleSourceEq p q))
    (anchorNode (eqToIso (projection_first_source_eq p q (𝟙 C) (q ≫ p) rfl))
      ⟨BinaryNormalizationSimplex.targetMap (𝟙 C ≫ q) p,
        BinaryNormalizationSimplex.total (𝟙 C ≫ q) p⟩) = _
  rw [anchorNode_assoc, Iso.trans_assoc, eqToIso_trans]
  exact binary_target_transport p p q (𝟙 C ≫ q) rfl (Category.id_comp q).symm F δ

/-- The middle normalized chart source has exactly that same original binary total reference. -/
theorem rectangle_middle_source : rectangleNodes p q F δ 5 =
    ⟨BinaryNormalizationSimplex.targetMap q p, δ ≪≫ BinaryNormalizationSimplex.total q p⟩ := by
  unfold rectangleNodes
  rw [projection_middle_normal]
  change anchorNode (δ ≪≫ eqToIso (rectangleSourceEq p q))
    (anchorNode (eqToIso (projection_middle_source_eq p q q (𝟙 B) (𝟙 C)
      (by simp) (q ≫ p) rfl))
      ⟨BinaryNormalizationSimplex.targetMap q (𝟙 B ≫ p),
        BinaryNormalizationSimplex.total q (𝟙 B ≫ p)⟩) = _
  rw [anchorNode_assoc, Iso.trans_assoc, eqToIso_trans]
  exact binary_target_transport p (𝟙 B ≫ p) q q (Category.id_comp p).symm rfl F δ

/-- The original chart unit vertices with the unchanged polynomial precomposition. -/
def rectangleSideNodes (i : Fin 8) :
    Σ G : modelOf (boundedFlatPerfectWaldhausen A) ⟶
      modelOf (boundedFlatPerfectWaldhausen C), F.functor ≅ G.functor :=
  preReferenceNode F (sourceMap p) (δ ≪≫ BinaryNormalizationSimplex.total q p)
    ⟨vertices q i, references q i⟩

/-- The reference isomorphism to the precomposed first binary row. -/
def firstRowAnchor : F.functor ≅
    (sourceMap p ≫ BinaryNormalizationSimplex.sourceMap (𝟙 C) q).functor :=
  (δ ≪≫ eqToIso (rectangleSourceEq p q)) ≪≫
    rightRowReference (ProjectionReference.reference (𝟙 C) (q ≫ p)) (𝟙 C) q p
      (nativeFirstReference p q (𝟙 C) (q ≫ p) rfl)

/-- The reference isomorphism to the precomposed middle binary row. -/
def middleRowAnchor : F.functor ≅
    (sourceMap p ≫ BinaryNormalizationSimplex.sourceMap q (𝟙 B)).functor :=
  (δ ≪≫ eqToIso (rectangleSourceEq p q)) ≪≫
    rightRowReference (ProjectionReference.reference (𝟙 C) (q ≫ p)) q (𝟙 B) p
      (nativeMiddleReference p q q (𝟙 B) (𝟙 C) (by simp) (q ≫ p) rfl)

/-- The original first H0 row remains its genuine precomposed binary row. -/
theorem rectangle_first_row_form (i : Fin 3) :
    rectangleNodes p q F δ (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      preReferenceNode F (sourceMap p) (firstRowAnchor p q F δ)
        (binaryNodes (𝟙 C) q i) := by
  unfold rectangleNodes
  rw [native_first_right_row]
  exact anchor_pre_node _ _ _ _

/-- The other H0 chart row retains the actual middle-square reference transport. -/
theorem rectangle_middle_row_form (i : Fin 3) :
    rectangleNodes p q F δ (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
      preReferenceNode F (sourceMap p) (middleRowAnchor p q F δ)
        (binaryNodes q (𝟙 B) i) := by
  unfold rectangleNodes
  rw [native_middle_right_row]
  exact anchor_pre_node _ _ _ _

/-- The side's first unit row uses the same old binary normalization with source transport. -/
theorem rectangle_side_right_form (i : Fin 3) :
    rectangleSideNodes p q F δ (![0, 1, 2] i) =
      preReferenceNode F (sourceMap p)
        ((δ ≪≫ BinaryNormalizationSimplex.total q p) ≪≫
          isoWhiskerLeft (sourceMap p).functor (eqToIso (rightBinarySourceEq q)))
        (binaryNodes (𝟙 C) q i) := by
  unfold rectangleSideNodes
  rw [unit_right_row]
  exact pre_anchor_node _ _ _ _ _

/-- The other side row retains its separate original unit transport. -/
theorem rectangle_side_left_form (i : Fin 3) :
    rectangleSideNodes p q F δ (![0, 4, 5] i) =
      preReferenceNode F (sourceMap p)
        ((δ ≪≫ BinaryNormalizationSimplex.total q p) ≪≫
          isoWhiskerLeft (sourceMap p).functor (eqToIso (leftBinarySourceEq q)))
        (binaryNodes q (𝟙 B) i) := by
  unfold rectangleSideNodes
  rw [unit_left_row]
  exact pre_anchor_node _ _ _ _ _

/-- Equality of the complete source node identifies all three actual first-row nodes. -/
theorem rectangle_side_right (i : Fin 3) :
    rectangleNodes p q F δ (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      rectangleSideNodes p q F δ (![0, 1, 2] i) := by
  apply pre_families_match F (sourceMap p) (BinaryNormalizationSimplex.sourceMap (𝟙 C) q)
    (binaryNodes (𝟙 C) q) (rectangle_first_row_form p q F δ)
      (rectangle_side_right_form p q F δ) 0 ?_ i
  change rectangleNodes p q F δ 9 =
    preReferenceNode F (sourceMap p) (δ ≪≫ BinaryNormalizationSimplex.total q p)
      ⟨sourceMap q, Iso.refl _⟩
  exact (rectangle_first_source p q F δ).trans
    (preReferenceNode_source F (sourceMap p) (H := sourceMap q)
      (δ ≪≫ BinaryNormalizationSimplex.total q p)).symm

/-- The complete middle row follows from the same actual source and its native binary data. -/
theorem rectangle_side_left (i : Fin 3) :
    rectangleNodes p q F δ (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
      rectangleSideNodes p q F δ (![0, 4, 5] i) := by
  apply pre_families_match F (sourceMap p) (BinaryNormalizationSimplex.sourceMap q (𝟙 B))
    (binaryNodes q (𝟙 B)) (rectangle_middle_row_form p q F δ)
      (rectangle_side_left_form p q F δ) 0 ?_ i
  change rectangleNodes p q F δ 9 =
    preReferenceNode F (sourceMap p) (δ ≪≫ BinaryNormalizationSimplex.total q p)
      ⟨sourceMap q, Iso.refl _⟩
  exact (rectangle_first_source p q F δ).trans
    (preReferenceNode_source F (sourceMap p) (H := sourceMap q)
      (δ ≪≫ BinaryNormalizationSimplex.total q p)).symm

/-- The original polynomial unit vertices with the unchanged Laurent postcomposition. -/
def rectangleTopNodes (i : Fin 8) :
    Σ G : modelOf (boundedFlatPerfectWaldhausen A) ⟶
      modelOf (boundedFlatPerfectWaldhausen C), F.functor ≅ G.functor :=
  postReferenceNode F (sourceMap q) (δ ≪≫ BinaryNormalizationSimplex.total q p)
    ⟨vertices p i, references p i⟩

/-- The reference isomorphism to the postcomposed middle binary column. -/
def middleColumnAnchor : F.functor ≅
    (BinaryNormalizationSimplex.sourceMap (𝟙 B) p ≫ sourceMap q).functor :=
  (δ ≪≫ eqToIso (rectangleSourceEq p q)) ≪≫
    (nativeMiddleReference p q q (𝟙 B) (𝟙 C) (by simp) (q ≫ p) rfl ≪≫
      BinaryNormalizationSimplex.total q ((𝟙 B) ≫ p))

/-- The reference isomorphism to the postcomposed last binary column. -/
def lastColumnAnchor : F.functor ≅
    (BinaryNormalizationSimplex.sourceMap p (𝟙 A) ≫ sourceMap q).functor :=
  (δ ≪≫ eqToIso (rectangleSourceEq p q)) ≪≫
    (nativeLastReference p q p q (𝟙 A) (𝟙 B) (𝟙 C) (by simp) (by simp) (q ≫ p) rfl ≪≫
      BinaryNormalizationSimplex.total q (p ≫ (𝟙 A)))

/-- The first H0 polynomial column retains the actual binary normalization postmap. -/
theorem rectangle_middle_column_form (i : Fin 3) :
    rectangleNodes p q F δ (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
      postReferenceNode F (sourceMap q) (middleColumnAnchor p q F δ)
        (binaryNodes (𝟙 B) p i) := by
  unfold rectangleNodes
  rw [native_middle_column]
  exact anchor_post_node _ _ _ _

/-- The second column retains its separate original total-square reference transport. -/
theorem rectangle_last_column_form (i : Fin 3) :
    rectangleNodes p q F δ (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
      postReferenceNode F (sourceMap q) (lastColumnAnchor p q F δ)
        (binaryNodes p (𝟙 A) i) := by
  unfold rectangleNodes
  rw [native_last_column]
  exact anchor_post_node _ _ _ _

/-- The top's first row is precisely the original polynomial binary normalization. -/
theorem rectangle_top_right_form (i : Fin 3) :
    rectangleTopNodes p q F δ (![0, 1, 2] i) =
      postReferenceNode F (sourceMap q)
        ((δ ≪≫ BinaryNormalizationSimplex.total q p) ≪≫
          isoWhiskerRight (eqToIso (rightBinarySourceEq p)) (sourceMap q).functor)
        (binaryNodes (𝟙 B) p i) := by
  unfold rectangleTopNodes
  rw [unit_right_row]
  exact post_anchor_node _ _ _ _ _

/-- The other top row retains the original left unit source equality. -/
theorem rectangle_top_left_form (i : Fin 3) :
    rectangleTopNodes p q F δ (![0, 4, 5] i) =
      postReferenceNode F (sourceMap q)
        ((δ ≪≫ BinaryNormalizationSimplex.total q p) ≪≫
          isoWhiskerRight (eqToIso (leftBinarySourceEq p)) (sourceMap q).functor)
        (binaryNodes p (𝟙 A) i) := by
  unfold rectangleTopNodes
  rw [unit_left_row]
  exact post_anchor_node _ _ _ _ _

/-- All three first-column nodes follow from the full common source and original binary data. -/
theorem rectangle_top_right (i : Fin 3) :
    rectangleNodes p q F δ (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
      rectangleTopNodes p q F δ (![0, 1, 2] i) := by
  apply post_families_match F (sourceMap q) (BinaryNormalizationSimplex.sourceMap (𝟙 B) p)
    (binaryNodes (𝟙 B) p) (rectangle_middle_column_form p q F δ)
      (rectangle_top_right_form p q F δ) 0 ?_ i
  change rectangleNodes p q F δ 5 =
    postReferenceNode F (sourceMap q) (δ ≪≫ BinaryNormalizationSimplex.total q p)
      ⟨sourceMap p, Iso.refl _⟩
  exact (rectangle_middle_source p q F δ).trans
    (postReferenceNode_source F (sourceMap q) (H := sourceMap p)
      (δ ≪≫ BinaryNormalizationSimplex.total q p)).symm

/-- The original last column shares its complete source, not merely its realized endpoint. -/
theorem rectangle_top_left (i : Fin 3) :
    rectangleNodes p q F δ (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
      rectangleTopNodes p q F δ (![0, 4, 5] i) := by
  apply post_families_match F (sourceMap q) (BinaryNormalizationSimplex.sourceMap p (𝟙 A))
    (binaryNodes p (𝟙 A)) (rectangle_last_column_form p q F δ)
      (rectangle_top_left_form p q F δ) 0 ?_ i
  change rectangleNodes p q F δ 5 =
    postReferenceNode F (sourceMap q) (δ ≪≫ BinaryNormalizationSimplex.total q p)
      ⟨sourceMap p, Iso.refl _⟩
  exact (rectangle_middle_source p q F δ).trans
    (postReferenceNode_source F (sourceMap q) (H := sourceMap p)
      (δ ≪≫ BinaryNormalizationSimplex.total q p)).symm

/-- The reference isomorphism to the first normalized triple composite. -/
def firstTripleAnchor : F.functor ≅ (NormalizedTripleSimplex.sourceMap (𝟙 C) q p).functor :=
  (δ ≪≫ eqToIso (rectangleSourceEq p q)) ≪≫
    nativeFirstReference p q (𝟙 C) (q ≫ p) rfl

/-- The reference isomorphism to the last normalized triple composite. -/
def lastTripleAnchor : F.functor ≅ (NormalizedTripleSimplex.sourceMap q p (𝟙 A)).functor :=
  (δ ≪≫ eqToIso (rectangleSourceEq p q)) ≪≫
    nativeLastReference p q p q (𝟙 A) (𝟙 B) (𝟙 C) (by simp) (by simp) (q ≫ p) rfl

/-- Every original first-triple node retains its complete equality and reference transport. -/
theorem rectangle_first_triple (i : Fin 8) :
    rectangleNodes p q F δ (DoubleSquareMergedSimplex.firstFace.toOrderHom i) =
      ⟨SplitTripleSimplex.vertices (𝟙 C) q p i,
        firstTripleAnchor p q F δ ≪≫ SplitTripleSimplex.references (𝟙 C) q p i⟩ := by
  have h := congrArg (anchorNode δ)
    (projection_first_nodes p q p q (𝟙 A) (𝟙 B) (𝟙 C) (by simp) (by simp)
      (q ≫ p) rfl (BinaryNormalizationSimplex.sourceMap q p) (rectangleSourceEq p q) i)
  simpa only [rectangleNodes, projectionNativeNode, ModelSimplex.reanchorNodes, anchorNode,
    projectionFirstReference, firstTripleAnchor, nativeFirstReference, Iso.trans_assoc] using h

/-- Every last-triple node keeps the actual total-square transport before its transformations. -/
theorem rectangle_last_triple (i : Fin 8) :
    rectangleNodes p q F δ (DoubleSquareMergedSimplex.lastFace.toOrderHom i) =
      ⟨SplitTripleSimplex.vertices q p (𝟙 A) i,
        lastTripleAnchor p q F δ ≪≫ SplitTripleSimplex.references q p (𝟙 A) i⟩ := by
  have h := congrArg (anchorNode (δ ≪≫ eqToIso (rectangleSourceEq p q)))
    (native_last_nodes p q p q (𝟙 A) (𝟙 B) (𝟙 C) (by simp) (by simp) (q ≫ p) rfl i)
  simpa only [rectangleNodes, anchorNode, lastTripleAnchor, Iso.trans_assoc] using h

/-- The first-triple reference followed by its source-column normalization. -/
def sourceColumnAnchor : F.functor ≅
    (BinaryNormalizationSimplex.sourceMap q p ≫ sourceMap (𝟙 C)).functor :=
  firstTripleAnchor p q F δ ≪≫ BinaryNormalizationSimplex.total (𝟙 C) (q ≫ p)

/-- The target-row reference induced by the last-triple reference. -/
def targetRowAnchor : F.functor ≅
    (sourceMap (𝟙 A) ≫ BinaryNormalizationSimplex.sourceMap q p).functor :=
  rightRowReference F q p (𝟙 A) (lastTripleAnchor p q F δ)

/-- The entire original source projection path is a fixed postcomposed binary column. -/
theorem rectangle_source_column_form (i : Fin 3) :
    rectangleNodes p q F δ (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
      postReferenceNode F (sourceMap (𝟙 C)) (sourceColumnAnchor p q F δ)
        (binaryNodes q p i) :=
  (rectangle_first_triple p q F δ (leftIndex i)).trans
    (triple_left_column_iso F (𝟙 C) q p (firstTripleAnchor p q F δ) i)

/-- The entire original target projection path is a fixed precomposed binary row. -/
theorem rectangle_target_row_form (i : Fin 3) :
    rectangleNodes p q F δ (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) =
      preReferenceNode F (sourceMap (𝟙 A)) (targetRowAnchor p q F δ)
        (binaryNodes q p i) :=
  (rectangle_last_triple p q F δ (rightIndex i)).trans
    (triple_right_row F q p (𝟙 A) (lastTripleAnchor p q F δ) i)

end Rectangle

private theorem rectangle_identity_transport {A B C : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (a₀ : A ⟶ A) (b₀ : B ⟶ B) (c₀ : C ⟶ C)
    (ha₀ : a₀ = 𝟙 A) (hb₀ : b₀ = 𝟙 B) (hc₀ : c₀ = 𝟙 C)
    (hp : b₀ ≫ p = p ≫ a₀) (hq : c₀ ≫ q = q ≫ b₀)
    (r : C ⟶ A) (hr : q ≫ p = r)
    (F G : modelOf (boundedFlatPerfectWaldhausen A) ⟶
      modelOf (boundedFlatPerfectWaldhausen C)) (ρ : F.functor ≅ G.functor)
    (e : G.functor = (ProjectionReference.reference c₀ r).functor)
    (d : G.functor = (BinaryNormalizationSimplex.sourceMap q p).functor) (i : Fin 18) :
    anchorNode (ρ ≪≫ eqToIso e)
        (ProjectionReference.nodes p q p q a₀ b₀ c₀ hp hq r hr i) =
      rectangleNodes p q F (ρ ≪≫ eqToIso d) i := by
  subst a₀
  subst b₀
  subst c₀
  subst r
  unfold rectangleNodes
  rw [Iso.trans_assoc, eqToIso_trans]

variable {R : CommRingCat.{u}} (P : Over (Spec R)) (a : Under R)

/-- Exact geometric transport from the fixed original projection to the original H0 source. -/
theorem h0SourceEq : (BassProjectionPath.source P a).functor =
    (BassH0Diagram.reference P (𝟙 a)).functor :=
  congrArg (fun G ↦ AsSmall.down ⋙ G ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (by
      rw [CategoryTheory.Functor.map_id, boundedFlatCoefficientGeometricIdentity, Category.id_comp]
      exact laurentPlus_projection P a))

/-- One common anchor for all thirty-one original H0 nodes. -/
def h0SourceIso : (source P a).functor ≅ (BassH0Diagram.reference P (𝟙 a)).functor :=
  sourceToProjection P a ≪≫ eqToIso (h0SourceEq P a)

/-- All original H0 vertices and references, without replacing their original scalar family. -/
def h0Nodes (i : Fin 31) : Node P a :=
  anchorNode (h0SourceIso P a) (BassH0Diagram.nodes P (𝟙 a) i)

/-- The entire H0 simplex survives its common-reference transport literally. -/
theorem h0_family :
    ModelSimplex.ofIsos (source P a) (fun i ↦ (h0Nodes P a i).1)
      (fun i ↦ (h0Nodes P a i).2) = BassH0Diagram.simplex P (𝟙 a) :=
  anchored_family (h0SourceIso P a) (BassH0Diagram.nodes P (𝟙 a))

variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)

include ha in
/-- The actual projection equation transports the common source to either chart factorization. -/
theorem chartProjectionEq : (BassProjectionPath.source P a).functor =
    (BinaryNormalizationSimplex.sourceMap (coefficientMap P (α.app a))
      (polynomialProjection P a)).functor :=
  congrArg (fun G ↦ AsSmall.down ⋙ G ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback ((laurentPlus_projection P a).trans ha.symm))

/-- The chart factorization reference retains the original positive/inverse projection equality. -/
def chartProjectionIso : (source P a).functor ≅
    (BinaryNormalizationSimplex.sourceMap (coefficientMap P (α.app a))
      (polynomialProjection P a)).functor :=
  sourceToProjection P a ≪≫ eqToIso (chartProjectionEq P a α ha)

/-- Both coefficient rectangles are reanchored through the same original H0 source. -/
def chartNodes (i : Fin 18) : Node P a :=
  anchorNode (h0SourceIso P a) (BassH0Diagram.chartNodes P (𝟙 a) α ha i)

/-- Coefficient identity transports preserve every actual rectangle node and its reference. -/
theorem chart_identity (i : Fin 18) : chartNodes P a α ha i =
    rectangleNodes (polynomialProjection P a) (coefficientMap P (α.app a))
      (source P a) (chartProjectionIso P a α ha) i := by
  exact rectangle_identity_transport (polynomialProjection P a) (coefficientMap P (α.app a))
    (coefficientMap P (𝟙 a)) (coefficientMap P ((polynomialUnderFunctor R).map (𝟙 a)))
    (coefficientMap P ((laurentUnderFunctor R).map (𝟙 a)))
    (boundedFlatCoefficientGeometricIdentity P a)
    ((congrArg (coefficientMap P) ((polynomialUnderFunctor R).map_id a)).trans
      (boundedFlatCoefficientGeometricIdentity P _))
    ((congrArg (coefficientMap P) ((laurentUnderFunctor R).map_id a)).trans
      (boundedFlatCoefficientGeometricIdentity P _))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (polynomialUnderCoefficient R) (𝟙 a))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α (𝟙 a))
      (laurentProjection P a) ha
    (source P a) (BassProjectionPath.source P a) (sourceToProjection P a)
    (h0SourceEq P a) (chartProjectionEq P a α ha) i

/-- The first native chart source is its original normalized total, with full transport. -/
theorem chart_first_source : chartNodes P a α ha 9 =
    ⟨BinaryNormalizationSimplex.targetMap (coefficientMap P (α.app a))
      (polynomialProjection P a), chartProjectionIso P a α ha ≪≫
        BinaryNormalizationSimplex.total (coefficientMap P (α.app a))
          (polynomialProjection P a)⟩ :=
  (chart_identity P a α ha 9).trans (rectangle_first_source _ _ _ _)

/-- The two native rectangle rows retain the same normalized source and original reference. -/
theorem chart_middle_source : chartNodes P a α ha 5 =
    ⟨BinaryNormalizationSimplex.targetMap (coefficientMap P (α.app a))
      (polynomialProjection P a), chartProjectionIso P a α ha ≪≫
        BinaryNormalizationSimplex.total (coefficientMap P (α.app a))
          (polynomialProjection P a)⟩ :=
  (chart_identity P a α ha 5).trans (rectangle_middle_source _ _ _ _)

/-- The positive chart projection total is exactly the existing top/side anchor. -/
theorem plus_total_anchor :
    chartProjectionIso P a (underToLaurent R) (laurentPlus_projection P a) ≪≫
      BinaryNormalizationSimplex.total (laurentPlus P a) (polynomialProjection P a) =
        plusSourceIso P a := by
  rw [plus_anchor]
  change (sourceToProjection P a ≪≫ eqToIso rfl) ≪≫
      BinaryNormalizationSimplex.total (laurentPlus P a) (polynomialProjection P a) =
    sourceToProjection P a ≪≫
      BinaryNormalizationSimplex.total (laurentPlus P a) (polynomialProjection P a)
  simp only [eqToIso_refl, Iso.trans_refl]

/-- The inverse chart uses its actual source transport before the unchanged binary total. -/
theorem minus_total_anchor :
    chartProjectionIso P a (underToLaurentInvert R) (laurentMinus_projection P a) ≪≫
      BinaryNormalizationSimplex.total (laurentMinus P a) (polynomialProjection P a) =
        minusSourceIso P a := by
  rw [minus_anchor]
  change (sourceToProjection P a ≪≫ BassProjectionPath.sourceIso P a) ≪≫ _ =
    sourceToProjection P a ≪≫ (BassProjectionPath.sourceIso P a ≪≫ _)
  exact Iso.trans_assoc _ _ _

/-- Original positive projection-rectangle slots retain the common H0 anchor. -/
theorem h0_plus_nodes (i : Fin 18) :
    h0Nodes P a (BassH0Diagram.plusFace.toOrderHom i) =
      chartNodes P a (underToLaurent R) (laurentPlus_projection P a) i :=
  congrArg (anchorNode (h0SourceIso P a)) (BassH0Diagram.plus_nodes P (𝟙 a) i)

/-- Original inverse slots keep their separate chart while sharing the same H0 anchor. -/
theorem h0_minus_nodes (i : Fin 18) :
    h0Nodes P a (BassH0Diagram.minusFace.toOrderHom i) =
      chartNodes P a (underToLaurentInvert R) (laurentMinus_projection P a) i :=
  congrArg (anchorNode (h0SourceIso P a)) (BassH0Diagram.minus_nodes P (𝟙 a) i)

/-- Both original lower positive chart rows retain all their actual reference nodes. -/
theorem plus_side_right (i : Fin 3) :
    chartNodes P a (underToLaurent R) (laurentPlus_projection P a)
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      plusSideNodes P a (![0, 1, 2] i) := by
  exact (chart_identity P a (underToLaurent R) (laurentPlus_projection P a) _).trans
    ((rectangle_side_right _ _ _ _ i).trans
    (congrArg (fun ρ ↦ preReferenceNode (source P a) (sourceMap (polynomialProjection P a))
      ρ ⟨vertices (laurentPlus P a) (![0, 1, 2] i), references (laurentPlus P a) (![0, 1, 2] i)⟩)
      (plus_total_anchor P a)))

theorem plus_side_left (i : Fin 3) :
    chartNodes P a (underToLaurent R) (laurentPlus_projection P a)
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
      plusSideNodes P a (![0, 4, 5] i) := by
  exact (chart_identity P a (underToLaurent R) (laurentPlus_projection P a) _).trans
    ((rectangle_side_left _ _ _ _ i).trans
    (congrArg (fun ρ ↦ preReferenceNode (source P a) (sourceMap (polynomialProjection P a))
      ρ ⟨vertices (laurentPlus P a) (![0, 4, 5] i), references (laurentPlus P a) (![0, 4, 5] i)⟩)
      (plus_total_anchor P a)))

/-- The inverse chart retains its own two original binary rows and their full references. -/
theorem minus_side_right (i : Fin 3) :
    chartNodes P a (underToLaurentInvert R) (laurentMinus_projection P a)
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (rightIndex i)) =
      minusSideNodes P a (![0, 1, 2] i) := by
  exact (chart_identity P a (underToLaurentInvert R) (laurentMinus_projection P a) _).trans
    ((rectangle_side_right _ _ _ _ i).trans
    (congrArg (fun ρ ↦ preReferenceNode (source P a) (sourceMap (polynomialProjection P a))
      ρ ⟨vertices (laurentMinus P a) (![0, 1, 2] i), references (laurentMinus P a) (![0, 1, 2] i)⟩)
      (minus_total_anchor P a)))

theorem minus_side_left (i : Fin 3) :
    chartNodes P a (underToLaurentInvert R) (laurentMinus_projection P a)
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (rightIndex i)) =
      minusSideNodes P a (![0, 4, 5] i) := by
  exact (chart_identity P a (underToLaurentInvert R) (laurentMinus_projection P a) _).trans
    ((rectangle_side_left _ _ _ _ i).trans
    (congrArg (fun ρ ↦ preReferenceNode (source P a) (sourceMap (polynomialProjection P a))
      ρ ⟨vertices (laurentMinus P a) (![0, 4, 5] i), references (laurentMinus P a) (![0, 4, 5] i)⟩)
      (minus_total_anchor P a)))

/-- The positive polynomial columns use the exact original top-square nodes. -/
theorem plus_top_right (i : Fin 3) :
    chartNodes P a (underToLaurent R) (laurentPlus_projection P a)
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
      plusNodes P a (![0, 1, 2] i) := by
  exact (chart_identity P a (underToLaurent R) (laurentPlus_projection P a) _).trans
    ((rectangle_top_right _ _ _ _ i).trans
    (congrArg (fun ρ ↦ postReferenceNode (source P a) (sourceMap (laurentPlus P a))
      ρ ⟨vertices (polynomialProjection P a) (![0, 1, 2] i),
        references (polynomialProjection P a) (![0, 1, 2] i)⟩) (plus_total_anchor P a)))

theorem plus_top_left (i : Fin 3) :
    chartNodes P a (underToLaurent R) (laurentPlus_projection P a)
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
      plusNodes P a (![0, 4, 5] i) := by
  exact (chart_identity P a (underToLaurent R) (laurentPlus_projection P a) _).trans
    ((rectangle_top_left _ _ _ _ i).trans
    (congrArg (fun ρ ↦ postReferenceNode (source P a) (sourceMap (laurentPlus P a))
      ρ ⟨vertices (polynomialProjection P a) (![0, 4, 5] i),
        references (polynomialProjection P a) (![0, 4, 5] i)⟩) (plus_total_anchor P a)))

/-- The inverse polynomial columns keep their distinct original top-square references. -/
theorem minus_top_right (i : Fin 3) :
    chartNodes P a (underToLaurentInvert R) (laurentMinus_projection P a)
      (DoubleSquareMergedSimplex.middleFace.toOrderHom (leftIndex i)) =
      minusNodes P a (![0, 1, 2] i) := by
  exact (chart_identity P a (underToLaurentInvert R) (laurentMinus_projection P a) _).trans
    ((rectangle_top_right _ _ _ _ i).trans
    (congrArg (fun ρ ↦ postReferenceNode (source P a) (sourceMap (laurentMinus P a))
      ρ ⟨vertices (polynomialProjection P a) (![0, 1, 2] i),
        references (polynomialProjection P a) (![0, 1, 2] i)⟩) (minus_total_anchor P a)))

theorem minus_top_left (i : Fin 3) :
    chartNodes P a (underToLaurentInvert R) (laurentMinus_projection P a)
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (leftIndex i)) =
      minusNodes P a (![0, 4, 5] i) := by
  exact (chart_identity P a (underToLaurentInvert R) (laurentMinus_projection P a) _).trans
    ((rectangle_top_left _ _ _ _ i).trans
    (congrArg (fun ρ ↦ postReferenceNode (source P a) (sourceMap (laurentMinus P a))
      ρ ⟨vertices (polynomialProjection P a) (![0, 4, 5] i),
        references (polynomialProjection P a) (![0, 4, 5] i)⟩) (minus_total_anchor P a)))

/-- The positive projection row consists of the three unchanged original binary nodes. -/
theorem projection_plus_row (i : Fin 3) :
    BassProjectionPath.nodes P a (![0, 1, 2] i) =
      binaryNodes (laurentPlus P a) (polynomialProjection P a) i := by
  fin_cases i <;> rfl

/-- The inverse row retains its original source transport before either normalization step. -/
theorem projection_minus_row (i : Fin 3) :
    BassProjectionPath.nodes P a (![0, 3, 4] i) =
      anchorNode (BassProjectionPath.sourceIso P a)
        (binaryNodes (laurentMinus P a) (polynomialProjection P a) i) := by
  fin_cases i
  · apply ModelSimplex.reference_node_eq (BassProjectionPath.source_eq P a)
    simp [BassProjectionPath.sourceIso, binaryNodes]
  · rfl
  · rfl

/-- The actual initial bottom column is the original Bass nodes under fixed Laurent identity. -/
theorem bottom_initial_column (j : Fin 5) :
    bottomNodes P a (Quillen.SimplexGrid.index 4 2 (j, 0)) =
      postReferenceNode (source P a)
        (unitSourceMap (space (op P, (laurentUnderFunctor R).obj a))) (bottomSourceIso P a)
        (BassProjectionPath.nodes P a j) := by
  have h := product_column_nodes (source P a) (BassProjectionPath.source P a)
    (fun i ↦ (BassProjectionPath.nodes P a i).1) (fun i ↦ (BassProjectionPath.nodes P a i).2)
    (unitSourceMap (space (op P, (laurentUnderFunctor R).obj a)))
    (CoefficientPolynomialSpanUnitSimplex.identityVertices
      (space (op P, (laurentUnderFunctor R).obj a)))
    (CoefficientPolynomialSpanUnitSimplex.identityReferences
      (space (op P, (laurentUnderFunctor R).obj a))) (bottomSourceIso P a) j 0
  change bottomNodes P a (Quillen.SimplexGrid.index 4 2 (j, 0)) =
    postReferenceNode (source P a)
      (unitSourceMap (space (op P, (laurentUnderFunctor R).obj a)))
      (bottomSourceIso P a ≪≫ isoWhiskerLeft (BassProjectionPath.source P a).functor
        (Iso.refl _)) (BassProjectionPath.nodes P a j) at h
  exact h.trans (post_identity_anchor (source P a) (BassProjectionPath.source P a)
    (unitSourceMap (space (op P, (laurentUnderFunctor R).obj a))) (bottomSourceIso P a)
    (BassProjectionPath.nodes P a j))

/-- The actual first top row is the same Bass node family under fixed original base identity. -/
theorem top_initial_row (j : Fin 5) :
    middleNodes P a (Quillen.SimplexGrid.index 2 4 (0, j)) =
      preReferenceNode (source P a) (unitSourceMap (space (op P, a))) (Iso.refl _)
        (BassProjectionPath.nodes P a j) := by
  have h := product_row_nodes (source P a) (unitSourceMap (space (op P, a)))
    (CoefficientPolynomialSpanUnitSimplex.identityVertices (space (op P, a)))
    (CoefficientPolynomialSpanUnitSimplex.identityReferences (space (op P, a)))
    (BassProjectionPath.source P a) (fun i ↦ (BassProjectionPath.nodes P a i).1)
    (fun i ↦ (BassProjectionPath.nodes P a i).2) (Iso.refl _) 0 j
  change middleNodes P a (Quillen.SimplexGrid.index 2 4 (0, j)) =
    preReferenceNode (source P a) (unitSourceMap (space (op P, a)))
      (Iso.refl _ ≪≫ isoWhiskerRight (Iso.refl _) (BassProjectionPath.source P a).functor)
      (BassProjectionPath.nodes P a j) at h
  exact h.trans (pre_identity_anchor (source P a) (unitSourceMap (space (op P, a)))
    (BassProjectionPath.source P a) (Iso.refl _) (BassProjectionPath.nodes P a j))

theorem bottom_plus_form (i : Fin 3) :
    bottomNodes P a (Quillen.SimplexGrid.index 4 2 (![0, 1, 2] i, 0)) =
      postReferenceNode (source P a)
        (unitSourceMap (space (op P, (laurentUnderFunctor R).obj a))) (bottomSourceIso P a)
        (binaryNodes (laurentPlus P a) (polynomialProjection P a) i) := by
  rw [bottom_initial_column, projection_plus_row]

theorem bottom_minus_form (i : Fin 3) :
    bottomNodes P a (Quillen.SimplexGrid.index 4 2 (![0, 3, 4] i, 0)) =
      postReferenceNode (source P a)
        (unitSourceMap (space (op P, (laurentUnderFunctor R).obj a)))
        (bottomSourceIso P a ≪≫ isoWhiskerRight (BassProjectionPath.sourceIso P a)
          (unitSourceMap (space (op P, (laurentUnderFunctor R).obj a))).functor)
        (binaryNodes (laurentMinus P a) (polynomialProjection P a) i) := by
  rw [bottom_initial_column, projection_minus_row]
  exact post_anchor_node _ _ _ _ _

theorem top_plus_form (i : Fin 3) :
    middleNodes P a (Quillen.SimplexGrid.index 2 4 (0, ![0, 1, 2] i)) =
      preReferenceNode (source P a) (unitSourceMap (space (op P, a))) (Iso.refl _)
        (binaryNodes (laurentPlus P a) (polynomialProjection P a) i) := by
  rw [top_initial_row, projection_plus_row]

theorem top_minus_form (i : Fin 3) :
    middleNodes P a (Quillen.SimplexGrid.index 2 4 (0, ![0, 3, 4] i)) =
      preReferenceNode (source P a) (unitSourceMap (space (op P, a)))
        (isoWhiskerLeft (unitSourceMap (space (op P, a))).functor
          (BassProjectionPath.sourceIso P a))
        (binaryNodes (laurentMinus P a) (polynomialProjection P a) i) := by
  rw [top_initial_row, projection_minus_row, pre_anchor_node]
  simp only [Iso.refl_trans]

/-- Every positive source-projection node is its unchanged bottom-column node. -/
theorem plus_source_projection (i : Fin 3) :
    chartNodes P a (underToLaurent R) (laurentPlus_projection P a)
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
      bottomNodes P a (Quillen.SimplexGrid.index 4 2 (![0, 1, 2] i, 0)) := by
  apply post_families_match (source P a)
    (unitSourceMap (space (op P, (laurentUnderFunctor R).obj a)))
    (BinaryNormalizationSimplex.sourceMap (laurentPlus P a) (polynomialProjection P a))
    (binaryNodes (laurentPlus P a) (polynomialProjection P a))
    (fun j ↦ (chart_identity P a (underToLaurent R) (laurentPlus_projection P a) _).trans
      (rectangle_source_column_form _ _ _ _ j)) (bottom_plus_form P a) 2 ?_ i
  exact (plus_side_right P a 2).trans (plus_bottom_first P a)

/-- Every inverse source-projection node retains its separate original chart reference. -/
theorem minus_source_projection (i : Fin 3) :
    chartNodes P a (underToLaurentInvert R) (laurentMinus_projection P a)
      (DoubleSquareMergedSimplex.firstFace.toOrderHom (leftIndex i)) =
      bottomNodes P a (Quillen.SimplexGrid.index 4 2 (![0, 3, 4] i, 0)) := by
  apply post_families_match (source P a)
    (unitSourceMap (space (op P, (laurentUnderFunctor R).obj a)))
    (BinaryNormalizationSimplex.sourceMap (laurentMinus P a) (polynomialProjection P a))
    (binaryNodes (laurentMinus P a) (polynomialProjection P a))
    (fun j ↦ (chart_identity P a (underToLaurentInvert R) (laurentMinus_projection P a) _).trans
      (rectangle_source_column_form _ _ _ _ j)) (bottom_minus_form P a) 2 ?_ i
  exact (minus_side_right P a 2).trans (minus_bottom_first P a)

/-- Every positive target-projection node is the unchanged initial top-grid row. -/
theorem plus_target_projection (i : Fin 3) :
    chartNodes P a (underToLaurent R) (laurentPlus_projection P a)
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) =
      middleNodes P a (Quillen.SimplexGrid.index 2 4 (0, ![0, 1, 2] i)) := by
  apply pre_families_match (source P a) (unitSourceMap (space (op P, a)))
    (BinaryNormalizationSimplex.sourceMap (laurentPlus P a) (polynomialProjection P a))
    (binaryNodes (laurentPlus P a) (polynomialProjection P a))
    (fun j ↦ (chart_identity P a (underToLaurent R) (laurentPlus_projection P a) _).trans
      (rectangle_target_row_form _ _ _ _ j)) (top_plus_form P a) 2 ?_ i
  exact (plus_top_left P a 2).trans (plus_shared P a 0)

/-- The inverse target row retains both original raw and normalized comparison vertices. -/
theorem minus_target_projection (i : Fin 3) :
    chartNodes P a (underToLaurentInvert R) (laurentMinus_projection P a)
      (DoubleSquareMergedSimplex.lastFace.toOrderHom (rightIndex i)) =
      middleNodes P a (Quillen.SimplexGrid.index 2 4 (0, ![0, 3, 4] i)) := by
  apply pre_families_match (source P a) (unitSourceMap (space (op P, a)))
    (BinaryNormalizationSimplex.sourceMap (laurentMinus P a) (polynomialProjection P a))
    (binaryNodes (laurentMinus P a) (polynomialProjection P a))
    (fun j ↦ (chart_identity P a (underToLaurentInvert R) (laurentMinus_projection P a) _).trans
      (rectangle_target_row_form _ _ _ _ j)) (top_minus_form P a) 2 ?_ i
  exact (minus_top_left P a 2).trans (minus_shared P a 0)

/-- The five actual plus side boundary nodes, in their original path order. -/
theorem h0_plus_side (i : Fin 5) :
    h0Nodes P a (BassH0Diagram.plusFace.toOrderHom (![9, 10, 11, 12, 13] i)) =
      plusSideNodes P a (![0, 1, 2, 4, 5] i) := by
  rw [h0_plus_nodes]
  fin_cases i
  · exact plus_side_right P a 0
  · exact plus_side_right P a 1
  · exact plus_side_right P a 2
  · exact plus_side_left P a 1
  · exact plus_side_left P a 2

/-- The five actual plus top boundary nodes, in their original path order. -/
theorem h0_plus_top (i : Fin 5) :
    h0Nodes P a (BassH0Diagram.plusFace.toOrderHom (![5, 6, 13, 7, 17] i)) =
      plusNodes P a (![0, 1, 2, 4, 5] i) := by
  rw [h0_plus_nodes]
  fin_cases i
  · exact plus_top_right P a 0
  · exact plus_top_right P a 1
  · exact plus_top_right P a 2
  · exact plus_top_left P a 1
  · exact plus_top_left P a 2

/-- The three actual plus source projection nodes retain both binary normalization steps. -/
theorem h0_plus_source (i : Fin 3) :
    h0Nodes P a (BassH0Diagram.plusFace.toOrderHom (![2, 3, 11] i)) =
      bottomNodes P a (![0, 3, 6] i) := by
  rw [h0_plus_nodes]
  fin_cases i
  · exact plus_source_projection P a 0
  · exact plus_source_projection P a 1
  · exact plus_source_projection P a 2

/-- The three actual plus target projection nodes retain both binary normalization steps. -/
theorem h0_plus_target (i : Fin 3) :
    h0Nodes P a (BassH0Diagram.plusFace.toOrderHom (![15, 16, 17] i)) =
      middleNodes P a (![0, 1, 2] i) := by
  rw [h0_plus_nodes]
  fin_cases i
  · exact plus_target_projection P a 0
  · exact plus_target_projection P a 1
  · exact plus_target_projection P a 2

/-- The five actual minus side boundary nodes, in their original path order. -/
theorem h0_minus_side (i : Fin 5) :
    h0Nodes P a (BassH0Diagram.minusFace.toOrderHom (![9, 10, 11, 12, 13] i)) =
      minusSideNodes P a (![0, 1, 2, 4, 5] i) := by
  rw [h0_minus_nodes]
  fin_cases i
  · exact minus_side_right P a 0
  · exact minus_side_right P a 1
  · exact minus_side_right P a 2
  · exact minus_side_left P a 1
  · exact minus_side_left P a 2

/-- The five actual minus top boundary nodes, in their original path order. -/
theorem h0_minus_top (i : Fin 5) :
    h0Nodes P a (BassH0Diagram.minusFace.toOrderHom (![5, 6, 13, 7, 17] i)) =
      minusNodes P a (![0, 1, 2, 4, 5] i) := by
  rw [h0_minus_nodes]
  fin_cases i
  · exact minus_top_right P a 0
  · exact minus_top_right P a 1
  · exact minus_top_right P a 2
  · exact minus_top_left P a 1
  · exact minus_top_left P a 2

/-- The three actual minus source projection nodes retain both binary normalization steps. -/
theorem h0_minus_source (i : Fin 3) :
    h0Nodes P a (BassH0Diagram.minusFace.toOrderHom (![2, 3, 11] i)) =
      bottomNodes P a (![0, 9, 12] i) := by
  rw [h0_minus_nodes]
  fin_cases i
  · exact minus_source_projection P a 0
  · exact minus_source_projection P a 1
  · exact minus_source_projection P a 2

/-- The three actual minus target projection nodes retain both binary normalization steps. -/
theorem h0_minus_target (i : Fin 3) :
    h0Nodes P a (BassH0Diagram.minusFace.toOrderHom (![15, 16, 17] i)) =
      middleNodes P a (![0, 3, 4] i) := by
  rw [h0_minus_nodes]
  fin_cases i
  · exact minus_target_projection P a 0
  · exact minus_target_projection P a 1
  · exact minus_target_projection P a 2

end Quillen.PerfectComplexes.CoefficientBassUnitHZeroNodes
