/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCompositePathCells
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPolynomialSheetNormalizationComposition

/-!
# The original postcomposed direct endpoint in the radial triple sheet

Complete source-reference normalization commutes with the actual chart action on
its Laurent summand, both unchanged cylinder clocks, and its unreduced tip.
The original binary normalization word identifies the left radial endpoint.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPostcompRadialEndpoint
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier

private theorem whisker_triangle {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    (F F' : A ⥤ B) (M : B ⥤ C) (J : C ⥤ D) (H : B ⥤ D) (K : A ⥤ C)
    (δ : F' ≅ F) (γ : K ≅ F' ⋙ M) (ρ : H ≅ M ⋙ J) :
    isoWhiskerRight (γ ≪≫ isoWhiskerRight δ M) J ≪≫
      Functor.associator F M J ≪≫ isoWhiskerLeft F ρ.symm =
    (isoWhiskerRight γ J ≪≫ Functor.associator F' M J ≪≫
      isoWhiskerLeft F' ρ.symm) ≪≫ isoWhiskerRight δ H := by
  apply Iso.ext
  ext X
  have h := ρ.inv.naturality (δ.hom.app X)
  have hh := congrArg (fun k ↦ J.map (γ.hom.app X) ≫ k) h
  simpa only [Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.associator_hom_app,
    Iso.symm_hom, Functor.map_comp, Functor.comp_map, Category.comp_id,
    Category.id_comp, Category.assoc] using hh

private theorem node_triangle {V W T : Model.{v}}
    (D D' : V ⟶ W) (H K : W ⟶ T) (G : V ⟶ T)
    (δ : D'.functor ≅ D.functor) (γ : G.functor ≅ (D' ≫ H).functor)
    (ρ : H.functor ≅ K.functor) (N : Node D) :
    (⟨N.1 ≫ K, (γ ≪≫ isoWhiskerRight δ H.functor) ≪≫
      isoWhiskerLeft D.functor ρ ≪≫ isoWhiskerRight N.2 K.functor⟩ : Node G) =
    ⟨N.1 ≫ K, γ ≪≫ isoWhiskerLeft D'.functor ρ ≪≫
      isoWhiskerRight (δ ≪≫ N.2) K.functor⟩ := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Iso.ext
  ext X
  have h := ρ.hom.naturality (δ.hom.app X)
  have hh := congrArg (fun k ↦ γ.hom.app X ≫ k ≫ K.functor.map (N.2.hom.app X)) h
  simpa only [Iso.trans_hom, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.map_comp,
    Category.assoc] using hh

private theorem normalized_moving_node {V W T U : Model.{v}}
    (D D' : V ⟶ W) (M : W ⟶ T) (J : T ⟶ U) (H : W ⟶ U)
    (F : V ⟶ T) (G G' : V ⟶ U)
    (δ : D'.functor ≅ D.functor) (γ : F.functor ≅ (D' ≫ M).functor)
    (η : G.functor ≅ (D ≫ H).functor) (η' : G'.functor ≅ (D' ≫ H).functor)
    (ρ : H.functor ≅ (M ≫ J).functor) (N : Node D) (Z : Node H) :
    CommonReferenceProduct.reanchor (F₀ := F ≫ J)
      (isoWhiskerRight (γ ≪≫ isoWhiskerRight δ M.functor) J.functor ≪≫
        (η ≪≫ isoWhiskerLeft D.functor ρ ≪≫
          (Functor.associator D.functor M.functor J.functor).symm).symm)
      (⟨N.1 ≫ Z.1, η ≪≫ isoWhiskerLeft D.functor Z.2 ≪≫
        isoWhiskerRight N.2 Z.1.functor⟩ : Node G) =
    CommonReferenceProduct.reanchor (F₀ := F ≫ J)
      (isoWhiskerRight γ J.functor ≪≫
        (η' ≪≫ isoWhiskerLeft D'.functor ρ ≪≫
          (Functor.associator D'.functor M.functor J.functor).symm).symm)
      (⟨N.1 ≫ Z.1, η' ≪≫ isoWhiskerLeft D'.functor Z.2 ≪≫
        isoWhiskerRight (δ ≪≫ N.2) Z.1.functor⟩ : Node G') := by
  simp only [CommonReferenceProduct.reanchor, Iso.trans_symm, Iso.symm_symm_eq,
    isoWhiskerLeft_symm, Iso.trans_assoc, Iso.symm_self_id_assoc]
  have h := whisker_triangle D.functor D'.functor M.functor J.functor H.functor
    F.functor δ γ ρ
  have hn := node_triangle D D' H Z.1 (F ≫ J) δ
    (isoWhiskerRight γ J.functor ≪≫ Functor.associator D'.functor M.functor J.functor ≪≫
      isoWhiskerLeft D'.functor ρ.symm) Z.2 N
  simpa only [← h, Iso.trans_assoc] using hn

private theorem normalized_laurent_word {A B C D E : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E]
    (F F' : A ⥤ B) (J₀ : B ⥤ C) (L : C ⥤ E) (M : B ⥤ D) (J₁ : D ⥤ E)
    (H : B ⥤ E) (K : A ⥤ D) (G : A ⥤ C)
    (δ : F' ≅ F) (γ : K ≅ F' ⋙ M) (ε : G ≅ F ⋙ J₀)
    (l : H ≅ J₀ ⋙ L) (r : H ≅ M ⋙ J₁) :
    isoWhiskerRight (γ ≪≫ isoWhiskerRight δ M) J₁ ≪≫
      (isoWhiskerRight ε L ≪≫ Functor.associator F J₀ L ≪≫
        isoWhiskerLeft F l.symm ≪≫ isoWhiskerLeft F r ≪≫
          (Functor.associator F M J₁).symm).symm =
    (isoWhiskerRight γ J₁ ≪≫
      (Functor.associator F' J₀ L ≪≫
        isoWhiskerLeft F' l.symm ≪≫ isoWhiskerLeft F' r ≪≫
          (Functor.associator F' M J₁).symm).symm) ≪≫
        isoWhiskerRight (isoWhiskerRight δ J₀ ≪≫ ε.symm) L := by
  apply Iso.ext
  ext X
  have h := (l.symm ≪≫ r).inv.naturality (δ.hom.app X)
  have hh := congrArg (fun k ↦ J₁.map (γ.hom.app X) ≫ k ≫ L.map (ε.inv.app X)) h
  simpa only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    isoWhiskerRight_hom, isoWhiskerRight_inv, isoWhiskerLeft_inv, isoWhiskerLeft_hom,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.map_comp, Functor.comp_map, Category.comp_id,
    Category.id_comp,
    Category.assoc] using hh

private def modelAnchor {V W T U Z : Model.{v}}
    (D : V ⟶ W) (J₀ : W ⟶ T) (L : T ⟶ Z) (M : W ⟶ U) (J₁ : U ⟶ Z)
    (H : W ⟶ Z) (G : V ⟶ T) (ε : G.functor ≅ (D ≫ J₀).functor)
    (l : H.functor ≅ (J₀ ≫ L).functor) (r : H.functor ≅ (M ≫ J₁).functor) :=
  (isoWhiskerRight ε L.functor ≪≫ Functor.associator D.functor J₀.functor L.functor ≪≫
    isoWhiskerLeft D.functor l.symm) ≪≫ isoWhiskerLeft D.functor r ≪≫
      (Functor.associator D.functor M.functor J₁.functor).symm

private theorem model_laurent_word {V W T U Z : Model.{v}}
    (D D' : V ⟶ W) (J₀ : W ⟶ T) (L : T ⟶ Z) (M : W ⟶ U) (J₁ : U ⟶ Z)
    (H : W ⟶ Z) (F : V ⟶ U) (G : V ⟶ T)
    (δ : D'.functor ≅ D.functor) (γ : F.functor ≅ (D' ≫ M).functor)
    (ε : G.functor ≅ (D ≫ J₀).functor)
    (l : H.functor ≅ (J₀ ≫ L).functor) (r : H.functor ≅ (M ≫ J₁).functor) :
    CoefficientBassPolynomialSheetNormalization.laurentIso (D ≫ M) F J₁ (G ≫ L)
      (modelAnchor D J₀ L M J₁ H G ε l r) (γ ≪≫ isoWhiskerRight δ M.functor) =
    CoefficientBassPolynomialSheetNormalization.laurentIso (D' ≫ M) F J₁ ((D' ≫ J₀) ≫ L)
      (modelAnchor D' J₀ L M J₁ H (D' ≫ J₀) (Iso.refl _) l r) γ ≪≫
        isoWhiskerRight (CoefficientBassPolynomialSheetNormalization.laurentIso
          D D' J₀ G ε δ) L.functor := by
  dsimp only [CoefficientBassPolynomialSheetNormalization.laurentIso, modelAnchor]
  simp only [Iso.trans_assoc, isoWhiskerRight_refl]
  have hr : Iso.refl ((D' ≫ J₀).functor ⋙ L.functor) ≪≫
      (Functor.associator D'.functor J₀.functor L.functor ≪≫
        isoWhiskerLeft D'.functor l.symm ≪≫ isoWhiskerLeft D'.functor r ≪≫
          (Functor.associator D'.functor M.functor J₁.functor).symm) =
      Functor.associator D'.functor J₀.functor L.functor ≪≫
        isoWhiskerLeft D'.functor l.symm ≪≫ isoWhiskerLeft D'.functor r ≪≫
          (Functor.associator D'.functor M.functor J₁.functor).symm :=
    Iso.refl_trans _
  rw [hr]
  simpa only [Iso.trans_assoc] using
    normalized_laurent_word D.functor D'.functor J₀.functor L.functor M.functor
      J₁.functor H.functor F.functor G.functor δ γ ε l r

private theorem binary_total_congr {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g g' : Y ⟶ Z)
    (h : g = g') :
    eqToIso (congrArg (fun k ↦ (BassH0Merge.normalizedMap k).functor)
      (congrArg (fun k ↦ f ≫ k) h)) ≪≫ BinaryNormalizationSimplex.total f g' =
    BinaryNormalizationSimplex.total f g ≪≫
      isoWhiskerRight (eqToIso (congrArg
        (fun k ↦ (BassH0Merge.normalizedMap k).functor) h))
        (BassH0Merge.normalizedMap f).functor := by
  subst g'
  simp only [eqToIso_refl, Iso.refl_trans, isoWhiskerRight_refl]
  exact (Iso.trans_refl _).symm

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The original left radial reference is precisely the postcomposed direct reference word. -/
theorem polynomial_word :
    CoefficientBassRaw1PolynomialRadialCaps.leftPolynomialIso P p q w ≪≫
      CoefficientBassRaw1PolynomialCompositeEndpoint.polynomialIso P (p ≫ q) w =
    CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w ≪≫
      isoWhiskerRight (CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P p q)
        (CoefficientBassSeedTargetChartAttachment.M P w).functor := by
  have h : CoefficientBassRaw1PolynomialTripleAnchor.polynomialArrow P q ≫
      CoefficientBassRaw1PolynomialTripleAnchor.polynomialArrow P p =
        CoefficientBassRaw1PolynomialTripleAnchor.polynomialArrow P (p ≫ q) := by
    simp only [CoefficientBassRaw1PolynomialTripleAnchor.polynomialArrow,
      Functor.map_comp, coefficientMap_comp]
  have hw := binary_total_congr
    (CoefficientBassRaw1PolynomialTripleAnchor.polynomialArrow P w) _ _ h
  change CoefficientBassRaw1PolynomialRadialCaps.leftPolynomialIso P p q w ≪≫
    (BinaryNormalizationSimplex.total _ _ ≪≫ isoWhiskerRight
      (Functor.leftUnitor (CoefficientBassSeedTargetChartAttachment.M P (p ≫ q)).functor).symm
      (CoefficientBassSeedTargetChartAttachment.M P w).functor) = _
  rw [← Iso.trans_assoc]
  have he : CoefficientBassRaw1PolynomialRadialCaps.leftPolynomialIso P p q w ≪≫
      BinaryNormalizationSimplex.total
        (CoefficientBassRaw1PolynomialTripleAnchor.polynomialArrow P w)
        (CoefficientBassRaw1PolynomialTripleAnchor.polynomialArrow P (p ≫ q)) =
    CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w ≪≫
      isoWhiskerRight (CoefficientBassRaw1PolynomialRadialCaps.pairPolynomialIso P p q)
        (CoefficientBassSeedTargetChartAttachment.M P w).functor := hw
  rw [he]
  simp only [CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso,
    isoWhiskerRight_trans, Iso.trans_assoc]
  rfl

namespace Positive
open CoefficientBassSeedTargetChartAttachment
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
  {V : Model.{u + 1}}
  (D D' : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (polynomialUnderFunctor R).obj a))))
  (F : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (polynomialUnderFunctor R).obj b))))
  (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (laurentUnderFunctor R).obj a))))
  (ε : G.functor ≅ (D ≫ Ja P (a := a)).functor)
  (δ : D'.functor ≅ D.functor) (γ : F.functor ≅ (D' ≫ M P f).functor)

private abbrev oldIso := γ ≪≫ isoWhiskerRight δ (M P f).functor
private abbrev sourceIso := CoefficientBassPolynomialSheetNormalization.laurentIso
  D D' (Ja P (a := a)) G ε δ
private abbrev oldLaurentIso := CoefficientBassPolynomialSheetNormalization.laurentIso
  (D ≫ M P f) F (Jb P (b := b)) (G ≫ L P f)
  (targetAnchor P f D G ε) (oldIso P f D D' F δ γ)
private abbrev newLaurentIso := CoefficientBassPolynomialSheetNormalization.laurentIso
  (D' ≫ M P f) F (Jb P (b := b)) ((D' ≫ Ja P (a := a)) ≫ L P f)
  (targetAnchor P f D' (D' ≫ Ja P (a := a)) (Iso.refl _)) γ
private abbrev oldNormalization := CoefficientBassPolynomialSheetNormalization.map
  (D ≫ M P f) F (Jb P (b := b)) (G ≫ L P f)
  (targetAnchor P f D G ε) (oldIso P f D D' F δ γ)
private abbrev newNormalization := CoefficientBassPolynomialSheetNormalization.map
  (D' ≫ M P f) F (Jb P (b := b)) ((D' ≫ Ja P (a := a)) ≫ L P f)
  (targetAnchor P f D' (D' ≫ Ja P (a := a)) (Iso.refl _)) γ
private abbrev sourceNormalization := CoefficientBassPolynomialSheetNormalization.map
  D D' (Ja P (a := a)) G ε δ

private theorem laurent_word :
    oldLaurentIso P f D D' F G ε δ γ =
      newLaurentIso P f D' F γ ≪≫
        isoWhiskerRight (sourceIso P D D' G ε δ) (L P f).functor := by
  exact model_laurent_word D D' (Ja P (a := a)) (L P f) (M P f)
    (Jb P (b := b)) (H P f) F G δ γ ε (leftIso P f) (rightIso P f)

private theorem moving_node (N : Node D) (i : Fin 5) :
    CommonReferenceProduct.reanchor (oldLaurentIso P f D D' F G ε δ γ)
      (movingNode P f D G ε N i) =
    CommonReferenceProduct.reanchor (newLaurentIso P f D' F γ)
      (movingNode P f D' (D' ≫ Ja P (a := a)) (Iso.refl _)
        (CommonReferenceProduct.reanchor δ N) i) := by
  exact normalized_moving_node D D' (M P f) (Jb P (b := b)) (H P f) F
    (G ≫ L P f) ((D' ≫ Ja P (a := a)) ≫ L P f) δ γ
    (squareAnchor P f D G ε) (squareAnchor P f D' (D' ≫ Ja P (a := a)) (Iso.refl _))
    (rightIso P f) N (NativeSquareFiveSimplex.nodes
      (coefficientMap P ((laurentUnderFunctor R).map f)) (laurentPlus P a)
      (laurentPlus P b) (coefficientMap P ((polynomialUnderFunctor R).map f))
      (coefficientMap_naturality P (underToLaurent R) f) i)

private theorem moving_parameter (y : |parameterSSet D|) (t : I) :
    mapParameter (CommonReferenceProduct.reanchor (oldLaurentIso P f D D' F G ε δ γ))
      (moving P f D G ε (y, t)) =
    mapParameter (CommonReferenceProduct.reanchor (newLaurentIso P f D' F γ))
      (moving P f D' (D' ≫ Ja P (a := a)) (Iso.refl _)
        (mapParameter (CommonReferenceProduct.reanchor δ) y, t)) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter D y
  change mapParameter _ (FiniteParameter.parameter _ _ _
    (parameter D N z, NativeSquareFiveSimplex.parameter t)) =
      mapParameter _ (FiniteParameter.parameter _ _ _
        (mapParameter _ (parameter D N z), NativeSquareFiveSimplex.parameter t))
  rw [mapParameter_parameter, FiniteParameter.parameter_characteristic,
    FiniteParameter.parameter_characteristic, mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun ns ↦ parameter (F ≫ Jb P (b := b)) ns
    (SimplexGrid.parameter k 4 (z, NativeSquareFiveSimplex.parameter t)))
  funext i
  exact moving_node P f D D' F G ε δ γ
    (N ((SimplexGrid.indexEquiv k 4).symm i).1) ((SimplexGrid.indexEquiv k 4).symm i).2

private theorem polynomial_parameter (y : |parameterSSet D|) :
    mapParameter (CommonReferenceProduct.reanchor (oldIso P f D D' F δ γ))
      (mapParameter (postcompNode (M P f)) y) =
    mapParameter (CommonReferenceProduct.reanchor γ)
      (mapParameter (postcompNode (M P f))
        (mapParameter (CommonReferenceProduct.reanchor δ) y)) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter D y
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun ns ↦ parameter F ns z)
  funext i
  rcases N i with ⟨K, ρ⟩
  simp only [CommonReferenceProduct.reanchor, postcompNode, oldIso,
    isoWhiskerRight_trans, Iso.trans_assoc]

private theorem laurent_parameter (y : |parameterSSet G|) :
    mapParameter (CommonReferenceProduct.reanchor (oldLaurentIso P f D D' F G ε δ γ))
      (mapParameter (postcompNode (L P f)) y) =
    mapParameter (CommonReferenceProduct.reanchor (newLaurentIso P f D' F γ))
      (mapParameter (postcompNode (L P f))
        (mapParameter (CommonReferenceProduct.reanchor (sourceIso P D D' G ε δ)) y)) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter G y
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun ns ↦ parameter (F ≫ Jb P (b := b)) ns z)
  funext i
  rw [laurent_word]
  rcases N i with ⟨K, ρ⟩
  simp only [CommonReferenceProduct.reanchor, postcompNode, isoWhiskerRight_trans,
    Iso.trans_assoc]

/-- Full source normalization commutes with the genuine positive first-sheet action. -/
private theorem action_normalization (z : |firstSimplicial D (Ja P (a := a)) G ε|) :
    oldNormalization P f D D' F G ε δ γ
      (CoefficientBassPositiveTargetSingleSheet.firstMap P f D G ε z) =
    newNormalization P f D' F γ
      (CoefficientBassPositiveTargetSingleSheet.firstMap P f D'
        (D' ≫ Ja P (a := a)) (Iso.refl _) (sourceNormalization P D D' G ε δ z)) := by
  have h : (fun z ↦ oldNormalization P f D D' F G ε δ γ
      (CoefficientBassPositiveTargetSingleSheet.firstMap P f D G ε z)) =
      (fun z ↦ newNormalization P f D' F γ
        (CoefficientBassPositiveTargetSingleSheet.firstMap P f D'
          (D' ≫ Ja P (a := a)) (Iso.refl _) (sourceNormalization P D D' G ε δ z))) := by
    apply FourEdgeTree.SetDescent.funext (attaching D (Ja P (a := a)) G ε) (erase D)
    · rintro ⟨y, ⟨t⟩⟩
      dsimp only
      rw [CoefficientBassPositiveTargetSingleSheet.firstMap_cylinder,
        CoefficientBassPolynomialSheetNormalization.map_cylinder,
        CoefficientBassPositiveTargetSingleSheet.firstMap_cylinder]
      rcases cover t with ⟨s, rfl⟩ | ⟨s, rfl⟩
      · change oldNormalization P f D D' F G ε δ γ
          (((CoefficientBassPositiveTargetSingleSheet.chartTrack P f D G ε false).trans
            (CoefficientBassPositiveTargetSingleSheet.contraction P f D G ε false))
            (lower s, y)) = _
        rw [ScalarRectangle.homotopy_lower, CoefficientBassPositiveTargetSingleSheet.nullTrack,
          ScalarRectangle.homotopy_lower]
        change oldNormalization P f D D' F G ε δ γ
          (SSet.toTop.map (left₀ (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
            (targetAnchor P f D G ε)) (moving P f D G ε (y, s))) =
          newNormalization P f D' F γ
            (SSet.toTop.map (left₀ (D' ≫ M P f) (Jb P (b := b))
              ((D' ≫ Ja P (a := a)) ≫ L P f)
              (targetAnchor P f D' (D' ≫ Ja P (a := a)) (Iso.refl _)))
              (moving P f D' (D' ≫ Ja P (a := a)) (Iso.refl _)
                (mapParameter (CommonReferenceProduct.reanchor δ) y, s)))
        rw [CoefficientBassPolynomialSheetNormalization.map_laurent,
          CoefficientBassPolynomialSheetNormalization.map_laurent]
        exact congrArg (SSet.toTop.map (left₀ F (Jb P (b := b))
          (F ≫ Jb P (b := b)) (Iso.refl _)))
          (moving_parameter P f D D' F G ε δ γ y s)
      · change oldNormalization P f D D' F G ε δ γ
          (((CoefficientBassPositiveTargetSingleSheet.chartTrack P f D G ε false).trans
            (CoefficientBassPositiveTargetSingleSheet.contraction P f D G ε false))
            (upper s, y)) = _
        rw [ScalarRectangle.homotopy_upper, CoefficientBassPositiveTargetSingleSheet.nullTrack,
          ScalarRectangle.homotopy_upper]
        change oldNormalization P f D D' F G ε δ γ
          (DoubleCylinder.realizedCylinder (attaching (D ≫ M P f) (Jb P (b := b))
            (G ≫ L P f) (targetAnchor P f D G ε)) (erase (D ≫ M P f))
            (mapParameter (postcompNode (M P f)) y, ULift.up s)) =
          newNormalization P f D' F γ
            (DoubleCylinder.realizedCylinder (attaching (D' ≫ M P f) (Jb P (b := b))
              ((D' ≫ Ja P (a := a)) ≫ L P f)
              (targetAnchor P f D' (D' ≫ Ja P (a := a)) (Iso.refl _)))
              (erase (D' ≫ M P f))
              (mapParameter (postcompNode (M P f))
                (mapParameter (CommonReferenceProduct.reanchor δ) y), ULift.up s))
        rw [CoefficientBassPolynomialSheetNormalization.map_cylinder,
          CoefficientBassPolynomialSheetNormalization.map_cylinder]
        exact congrArg (fun x ↦ DoubleCylinder.realizedCylinder
          (attaching F (Jb P (b := b)) (F ≫ Jb P (b := b)) (Iso.refl _)) (erase F)
          (x, ULift.up s)) (polynomial_parameter P f D D' F δ γ y)
    · intro y
      change oldNormalization P f D D' F G ε δ γ
        (CoefficientBassPositiveTargetSingleSheet.firstMap P f D G ε
          (SSet.toTop.map (left₀ D (Ja P (a := a)) G ε) y)) =
        newNormalization P f D' F γ
          (CoefficientBassPositiveTargetSingleSheet.firstMap P f D'
            (D' ≫ Ja P (a := a)) (Iso.refl _)
            (sourceNormalization P D D' G ε δ
              (SSet.toTop.map (left₀ D (Ja P (a := a)) G ε) y)))
      rw [CoefficientBassPositiveTargetSingleSheet.firstMap_laurent,
        CoefficientBassPolynomialSheetNormalization.map_laurent,
        CoefficientBassPositiveTargetSingleSheet.firstMap_laurent]
      change oldNormalization P f D D' F G ε δ γ
        (SSet.toTop.map (left₀ (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
          (targetAnchor P f D G ε)) (mapParameter (postcompNode (L P f)) y)) =
        newNormalization P f D' F γ
          (SSet.toTop.map (left₀ (D' ≫ M P f) (Jb P (b := b))
            ((D' ≫ Ja P (a := a)) ≫ L P f)
            (targetAnchor P f D' (D' ≫ Ja P (a := a)) (Iso.refl _)))
            (mapParameter (postcompNode (L P f))
              (mapParameter (CommonReferenceProduct.reanchor (sourceIso P D D' G ε δ)) y)))
      rw [CoefficientBassPolynomialSheetNormalization.map_laurent,
        CoefficientBassPolynomialSheetNormalization.map_laurent]
      exact congrArg (SSet.toTop.map (left₀ F (Jb P (b := b))
        (F ≫ Jb P (b := b)) (Iso.refl _))) (laurent_parameter P f D D' F G ε δ γ y)
    · intro y
      change oldNormalization P f D D' F G ε δ γ
        (CoefficientBassPositiveTargetSingleSheet.firstMap P f D G ε
          (SSet.toTop.map (right₀ D (Ja P (a := a)) G ε) y)) =
        newNormalization P f D' F γ
          (CoefficientBassPositiveTargetSingleSheet.firstMap P f D'
            (D' ≫ Ja P (a := a)) (Iso.refl _)
            (sourceNormalization P D D' G ε δ
              (SSet.toTop.map (right₀ D (Ja P (a := a)) G ε) y)))
      rw [CoefficientBassPositiveTargetSingleSheet.firstMap_tip,
        CoefficientBassPolynomialSheetNormalization.map_tip,
        CoefficientBassPositiveTargetSingleSheet.firstMap_tip]
      exact (CoefficientBassPolynomialSheetNormalization.map_tip _ _ _ _ _ _ _).trans
        (CoefficientBassPolynomialSheetNormalization.map_tip _ _ _ _ _ _ _).symm
  exact congrFun h z

/-- The genuine chart action commutes with complete source normalization on the actual sheet. -/
theorem firstMap_normalization (z : |firstSimplicial D (Ja P (a := a)) G ε|) :
    CoefficientBassPolynomialSheetNormalization.map
      (D ≫ M P f) F (Jb P (b := b)) (G ≫ L P f) (targetAnchor P f D G ε)
      (γ ≪≫ isoWhiskerRight δ (M P f).functor)
      (CoefficientBassPositiveTargetSingleSheet.firstMap P f D G ε z) =
    CoefficientBassPolynomialSheetNormalization.map
      (D' ≫ M P f) F (Jb P (b := b)) ((D' ≫ Ja P (a := a)) ≫ L P f)
      (targetAnchor P f D' (D' ≫ Ja P (a := a)) (Iso.refl _)) γ
      (CoefficientBassPositiveTargetSingleSheet.firstMap P f D'
        (D' ≫ Ja P (a := a)) (Iso.refl _)
        (CoefficientBassPolynomialSheetNormalization.map D D' (Ja P (a := a)) G ε δ z)) :=
  action_normalization P f D D' F G ε δ γ z

end Positive

namespace Negative
open CoefficientBassNegativeTargetChartAttachment
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
  {V : Model.{u + 1}}
  (D D' : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (polynomialUnderFunctor R).obj a))))
  (F : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (polynomialUnderFunctor R).obj b))))
  (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (laurentUnderFunctor R).obj a))))
  (ε : G.functor ≅ (D ≫ Ja P (a := a)).functor)
  (δ : D'.functor ≅ D.functor) (γ : F.functor ≅ (D' ≫ M P f).functor)

private abbrev oldIso := γ ≪≫ isoWhiskerRight δ (M P f).functor
private abbrev sourceIso := CoefficientBassPolynomialSheetNormalization.laurentIso
  D D' (Ja P (a := a)) G ε δ
private abbrev oldLaurentIso := CoefficientBassPolynomialSheetNormalization.laurentIso
  (D ≫ M P f) F (Jb P (b := b)) (G ≫ L P f)
  (targetAnchor P f D G ε) (oldIso P f D D' F δ γ)
private abbrev newLaurentIso := CoefficientBassPolynomialSheetNormalization.laurentIso
  (D' ≫ M P f) F (Jb P (b := b)) ((D' ≫ Ja P (a := a)) ≫ L P f)
  (targetAnchor P f D' (D' ≫ Ja P (a := a)) (Iso.refl _)) γ
private abbrev oldNormalization := CoefficientBassPolynomialSheetNormalization.map
  (D ≫ M P f) F (Jb P (b := b)) (G ≫ L P f)
  (targetAnchor P f D G ε) (oldIso P f D D' F δ γ)
private abbrev newNormalization := CoefficientBassPolynomialSheetNormalization.map
  (D' ≫ M P f) F (Jb P (b := b)) ((D' ≫ Ja P (a := a)) ≫ L P f)
  (targetAnchor P f D' (D' ≫ Ja P (a := a)) (Iso.refl _)) γ
private abbrev sourceNormalization := CoefficientBassPolynomialSheetNormalization.map
  D D' (Ja P (a := a)) G ε δ

private theorem laurent_word :
    oldLaurentIso P f D D' F G ε δ γ =
      newLaurentIso P f D' F γ ≪≫
        isoWhiskerRight (sourceIso P D D' G ε δ) (L P f).functor := by
  exact model_laurent_word D D' (Ja P (a := a)) (L P f) (M P f)
    (Jb P (b := b)) (H P f) F G δ γ ε (leftIso P f) (rightIso P f)

private theorem moving_node (N : Node D) (i : Fin 5) :
    CommonReferenceProduct.reanchor (oldLaurentIso P f D D' F G ε δ γ)
      (movingNode P f D G ε N i) =
    CommonReferenceProduct.reanchor (newLaurentIso P f D' F γ)
      (movingNode P f D' (D' ≫ Ja P (a := a)) (Iso.refl _)
        (CommonReferenceProduct.reanchor δ N) i) := by
  exact normalized_moving_node D D' (M P f) (Jb P (b := b)) (H P f) F
    (G ≫ L P f) ((D' ≫ Ja P (a := a)) ≫ L P f) δ γ
    (squareAnchor P f D G ε) (squareAnchor P f D' (D' ≫ Ja P (a := a)) (Iso.refl _))
    (rightIso P f) N (NativeSquareFiveSimplex.nodes
      (coefficientMap P ((laurentUnderFunctor R).map f)) (laurentMinus P a)
      (laurentMinus P b) (coefficientMap P ((polynomialUnderFunctor R).map f))
      (coefficientMap_naturality P (underToLaurentInvert R) f) i)

private theorem moving_parameter (y : |parameterSSet D|) (t : I) :
    mapParameter (CommonReferenceProduct.reanchor (oldLaurentIso P f D D' F G ε δ γ))
      (moving P f D G ε (y, t)) =
    mapParameter (CommonReferenceProduct.reanchor (newLaurentIso P f D' F γ))
      (moving P f D' (D' ≫ Ja P (a := a)) (Iso.refl _)
        (mapParameter (CommonReferenceProduct.reanchor δ) y, t)) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter D y
  change mapParameter _ (FiniteParameter.parameter _ _ _
    (parameter D N z, NativeSquareFiveSimplex.parameter t)) =
      mapParameter _ (FiniteParameter.parameter _ _ _
        (mapParameter _ (parameter D N z), NativeSquareFiveSimplex.parameter t))
  rw [mapParameter_parameter, FiniteParameter.parameter_characteristic,
    FiniteParameter.parameter_characteristic, mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun ns ↦ parameter (F ≫ Jb P (b := b)) ns
    (SimplexGrid.parameter k 4 (z, NativeSquareFiveSimplex.parameter t)))
  funext i
  exact moving_node P f D D' F G ε δ γ
    (N ((SimplexGrid.indexEquiv k 4).symm i).1) ((SimplexGrid.indexEquiv k 4).symm i).2

private theorem polynomial_parameter (y : |parameterSSet D|) :
    mapParameter (CommonReferenceProduct.reanchor (oldIso P f D D' F δ γ))
      (mapParameter (postcompNode (M P f)) y) =
    mapParameter (CommonReferenceProduct.reanchor γ)
      (mapParameter (postcompNode (M P f))
        (mapParameter (CommonReferenceProduct.reanchor δ) y)) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter D y
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun ns ↦ parameter F ns z)
  funext i
  rcases N i with ⟨K, ρ⟩
  simp only [CommonReferenceProduct.reanchor, postcompNode, oldIso,
    isoWhiskerRight_trans, Iso.trans_assoc]

private theorem laurent_parameter (y : |parameterSSet G|) :
    mapParameter (CommonReferenceProduct.reanchor (oldLaurentIso P f D D' F G ε δ γ))
      (mapParameter (postcompNode (L P f)) y) =
    mapParameter (CommonReferenceProduct.reanchor (newLaurentIso P f D' F γ))
      (mapParameter (postcompNode (L P f))
        (mapParameter (CommonReferenceProduct.reanchor (sourceIso P D D' G ε δ)) y)) := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter G y
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun ns ↦ parameter (F ≫ Jb P (b := b)) ns z)
  funext i
  rw [laurent_word]
  rcases N i with ⟨K, ρ⟩
  simp only [CommonReferenceProduct.reanchor, postcompNode, isoWhiskerRight_trans,
    Iso.trans_assoc]

/-- Full source normalization commutes with the genuine negative first-sheet action. -/
private theorem action_normalization (z : |firstSimplicial D (Ja P (a := a)) G ε|) :
    oldNormalization P f D D' F G ε δ γ
      (CoefficientBassNegativeTargetSingleSheet.firstMap P f D G ε z) =
    newNormalization P f D' F γ
      (CoefficientBassNegativeTargetSingleSheet.firstMap P f D'
        (D' ≫ Ja P (a := a)) (Iso.refl _) (sourceNormalization P D D' G ε δ z)) := by
  have h : (fun z ↦ oldNormalization P f D D' F G ε δ γ
      (CoefficientBassNegativeTargetSingleSheet.firstMap P f D G ε z)) =
      (fun z ↦ newNormalization P f D' F γ
        (CoefficientBassNegativeTargetSingleSheet.firstMap P f D'
          (D' ≫ Ja P (a := a)) (Iso.refl _) (sourceNormalization P D D' G ε δ z))) := by
    apply FourEdgeTree.SetDescent.funext (attaching D (Ja P (a := a)) G ε) (erase D)
    · rintro ⟨y, ⟨t⟩⟩
      dsimp only
      rw [CoefficientBassNegativeTargetSingleSheet.firstMap_cylinder,
        CoefficientBassPolynomialSheetNormalization.map_cylinder,
        CoefficientBassNegativeTargetSingleSheet.firstMap_cylinder]
      rcases cover t with ⟨s, rfl⟩ | ⟨s, rfl⟩
      · change oldNormalization P f D D' F G ε δ γ
          (((CoefficientBassNegativeTargetSingleSheet.chartTrack P f D G ε false).trans
            (CoefficientBassNegativeTargetSingleSheet.contraction P f D G ε false))
            (lower s, y)) = _
        rw [ScalarRectangle.homotopy_lower, CoefficientBassNegativeTargetSingleSheet.nullTrack,
          ScalarRectangle.homotopy_lower]
        change oldNormalization P f D D' F G ε δ γ
          (SSet.toTop.map (left₀ (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
            (targetAnchor P f D G ε)) (moving P f D G ε (y, s))) =
          newNormalization P f D' F γ
            (SSet.toTop.map (left₀ (D' ≫ M P f) (Jb P (b := b))
              ((D' ≫ Ja P (a := a)) ≫ L P f)
              (targetAnchor P f D' (D' ≫ Ja P (a := a)) (Iso.refl _)))
              (moving P f D' (D' ≫ Ja P (a := a)) (Iso.refl _)
                (mapParameter (CommonReferenceProduct.reanchor δ) y, s)))
        rw [CoefficientBassPolynomialSheetNormalization.map_laurent,
          CoefficientBassPolynomialSheetNormalization.map_laurent]
        exact congrArg (SSet.toTop.map (left₀ F (Jb P (b := b))
          (F ≫ Jb P (b := b)) (Iso.refl _)))
          (moving_parameter P f D D' F G ε δ γ y s)
      · change oldNormalization P f D D' F G ε δ γ
          (((CoefficientBassNegativeTargetSingleSheet.chartTrack P f D G ε false).trans
            (CoefficientBassNegativeTargetSingleSheet.contraction P f D G ε false))
            (upper s, y)) = _
        rw [ScalarRectangle.homotopy_upper, CoefficientBassNegativeTargetSingleSheet.nullTrack,
          ScalarRectangle.homotopy_upper]
        change oldNormalization P f D D' F G ε δ γ
          (DoubleCylinder.realizedCylinder (attaching (D ≫ M P f) (Jb P (b := b))
            (G ≫ L P f) (targetAnchor P f D G ε)) (erase (D ≫ M P f))
            (mapParameter (postcompNode (M P f)) y, ULift.up s)) =
          newNormalization P f D' F γ
            (DoubleCylinder.realizedCylinder (attaching (D' ≫ M P f) (Jb P (b := b))
              ((D' ≫ Ja P (a := a)) ≫ L P f)
              (targetAnchor P f D' (D' ≫ Ja P (a := a)) (Iso.refl _)))
              (erase (D' ≫ M P f))
              (mapParameter (postcompNode (M P f))
                (mapParameter (CommonReferenceProduct.reanchor δ) y), ULift.up s))
        rw [CoefficientBassPolynomialSheetNormalization.map_cylinder,
          CoefficientBassPolynomialSheetNormalization.map_cylinder]
        exact congrArg (fun x ↦ DoubleCylinder.realizedCylinder
          (attaching F (Jb P (b := b)) (F ≫ Jb P (b := b)) (Iso.refl _)) (erase F)
          (x, ULift.up s)) (polynomial_parameter P f D D' F δ γ y)
    · intro y
      change oldNormalization P f D D' F G ε δ γ
        (CoefficientBassNegativeTargetSingleSheet.firstMap P f D G ε
          (SSet.toTop.map (left₀ D (Ja P (a := a)) G ε) y)) =
        newNormalization P f D' F γ
          (CoefficientBassNegativeTargetSingleSheet.firstMap P f D'
            (D' ≫ Ja P (a := a)) (Iso.refl _)
            (sourceNormalization P D D' G ε δ
              (SSet.toTop.map (left₀ D (Ja P (a := a)) G ε) y)))
      rw [CoefficientBassNegativeTargetSingleSheet.firstMap_laurent,
        CoefficientBassPolynomialSheetNormalization.map_laurent,
        CoefficientBassNegativeTargetSingleSheet.firstMap_laurent]
      change oldNormalization P f D D' F G ε δ γ
        (SSet.toTop.map (left₀ (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
          (targetAnchor P f D G ε)) (mapParameter (postcompNode (L P f)) y)) =
        newNormalization P f D' F γ
          (SSet.toTop.map (left₀ (D' ≫ M P f) (Jb P (b := b))
            ((D' ≫ Ja P (a := a)) ≫ L P f)
            (targetAnchor P f D' (D' ≫ Ja P (a := a)) (Iso.refl _)))
            (mapParameter (postcompNode (L P f))
              (mapParameter (CommonReferenceProduct.reanchor (sourceIso P D D' G ε δ)) y)))
      rw [CoefficientBassPolynomialSheetNormalization.map_laurent,
        CoefficientBassPolynomialSheetNormalization.map_laurent]
      exact congrArg (SSet.toTop.map (left₀ F (Jb P (b := b))
        (F ≫ Jb P (b := b)) (Iso.refl _))) (laurent_parameter P f D D' F G ε δ γ y)
    · intro y
      change oldNormalization P f D D' F G ε δ γ
        (CoefficientBassNegativeTargetSingleSheet.firstMap P f D G ε
          (SSet.toTop.map (right₀ D (Ja P (a := a)) G ε) y)) =
        newNormalization P f D' F γ
          (CoefficientBassNegativeTargetSingleSheet.firstMap P f D'
            (D' ≫ Ja P (a := a)) (Iso.refl _)
            (sourceNormalization P D D' G ε δ
              (SSet.toTop.map (right₀ D (Ja P (a := a)) G ε) y)))
      rw [CoefficientBassNegativeTargetSingleSheet.firstMap_tip,
        CoefficientBassPolynomialSheetNormalization.map_tip,
        CoefficientBassNegativeTargetSingleSheet.firstMap_tip]
      exact (CoefficientBassPolynomialSheetNormalization.map_tip _ _ _ _ _ _ _).trans
        (CoefficientBassPolynomialSheetNormalization.map_tip _ _ _ _ _ _ _).symm
  exact congrFun h z

/-- The genuine chart action commutes with complete source normalization on the actual sheet. -/
theorem firstMap_normalization (z : |firstSimplicial D (Ja P (a := a)) G ε|) :
    CoefficientBassPolynomialSheetNormalization.map
      (D ≫ M P f) F (Jb P (b := b)) (G ≫ L P f) (targetAnchor P f D G ε)
      (γ ≪≫ isoWhiskerRight δ (M P f).functor)
      (CoefficientBassNegativeTargetSingleSheet.firstMap P f D G ε z) =
    CoefficientBassPolynomialSheetNormalization.map
      (D' ≫ M P f) F (Jb P (b := b)) ((D' ≫ Ja P (a := a)) ≫ L P f)
      (targetAnchor P f D' (D' ≫ Ja P (a := a)) (Iso.refl _)) γ
      (CoefficientBassNegativeTargetSingleSheet.firstMap P f D'
        (D' ≫ Ja P (a := a)) (Iso.refl _)
        (CoefficientBassPolynomialSheetNormalization.map D D' (Ja P (a := a)) G ε δ z)) :=
  action_normalization P f D D' F G ε δ γ z

end Negative

/-- The whole left radial plus endpoint is the actual postcomposition of the direct pair path. -/
theorem plus_left_one (s : I) :
    CoefficientBassRaw1PolynomialRadialCaps.left P (underToLaurent R) p q w (1, s) =
    CoefficientBassRaw1PolynomialPostcomp.plus P p q w
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurent R) p q (0, s)) := by
  change CoefficientBassRaw1PolynomialRadialCaps.leftMap P (underToLaurent R) p q w
    (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurent R) (p ≫ q) w (1, s)) = _
  rw [← CoefficientBassRaw1PolynomialCompositeEndpoint.plusPath_corrected_one,
    ← CoefficientBassRaw1PolynomialPairDirectAction.plusPath_corrected_zero]
  let D := (𝟙 (CoefficientBassRaw1PolynomialSourceCylinder.model P a)) ≫
    CoefficientBassSeedTargetChartAttachment.M P (p ≫ q)
  let G := CoefficientBassRaw1PolynomialSourceCylinder.reference P (underToLaurent R) a ≫
    CoefficientBassSeedTargetChartAttachment.L P (p ≫ q)
  let ε := CoefficientBassRaw1PolynomialCompositeEndpoint.plusFirstAnchor P (p ≫ q)
  let z := CoefficientBassPositiveTargetSingleSheet.firstMap P (p ≫ q)
    (𝟙 (CoefficientBassRaw1PolynomialSourceCylinder.model P a))
    (CoefficientBassRaw1PolynomialSourceCylinder.reference P (underToLaurent R) a) (Iso.refl _)
    (CoefficientBassRaw1PolynomialSourceCylinder.cylinder P (underToLaurent R) a s)
  have hn := CoefficientBassPolynomialSheetNormalization.map_comp
    (D ≫ CoefficientBassSeedTargetChartAttachment.M P w)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P (p ≫ q) w)
    (CoefficientBassRaw1PolynomialPostcomp.reference P p q w)
    (CoefficientBassSeedTargetChartAttachment.Jb P (b := d))
    (G ≫ CoefficientBassSeedTargetChartAttachment.L P w)
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P w D G ε)
    (CoefficientBassRaw1PolynomialCompositeEndpoint.polynomialIso P (p ≫ q) w)
    (CoefficientBassRaw1PolynomialRadialCaps.leftPolynomialIso P p q w)
    (CoefficientBassPositiveTargetSingleSheet.firstMap P w D G ε z)
  rw [polynomial_word] at hn
  have ha := Positive.action_normalization P w D
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassRaw1PolynomialPostcomp.reference P p q w) G ε
    (CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P p q)
    (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w) z
  exact hn.trans ha

/-- The whole left radial minus endpoint keeps its original chart and both original clocks. -/
theorem minus_left_one (s : I) :
    CoefficientBassRaw1PolynomialRadialCaps.left P (underToLaurentInvert R) p q w (1, s) =
    CoefficientBassRaw1PolynomialPostcomp.minus P p q w
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurentInvert R) p q (0, s)) := by
  change CoefficientBassRaw1PolynomialRadialCaps.leftMap P (underToLaurentInvert R) p q w
    (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurentInvert R)
      (p ≫ q) w (1, s)) = _
  rw [← CoefficientBassRaw1PolynomialCompositeEndpoint.minusPath_corrected_one,
    ← CoefficientBassRaw1PolynomialPairDirectAction.minusPath_corrected_zero]
  let D := (𝟙 (CoefficientBassRaw1PolynomialSourceCylinder.model P a)) ≫
    CoefficientBassNegativeTargetChartAttachment.M P (p ≫ q)
  let G := CoefficientBassRaw1PolynomialSourceCylinder.reference P (underToLaurentInvert R) a ≫
    CoefficientBassNegativeTargetChartAttachment.L P (p ≫ q)
  let ε := CoefficientBassRaw1PolynomialCompositeEndpoint.minusFirstAnchor P (p ≫ q)
  let z := CoefficientBassNegativeTargetSingleSheet.firstMap P (p ≫ q)
    (𝟙 (CoefficientBassRaw1PolynomialSourceCylinder.model P a))
    (CoefficientBassRaw1PolynomialSourceCylinder.reference P (underToLaurentInvert R) a)
    (Iso.refl _)
    (CoefficientBassRaw1PolynomialSourceCylinder.cylinder P (underToLaurentInvert R) a s)
  have hn := CoefficientBassPolynomialSheetNormalization.map_comp
    (D ≫ CoefficientBassNegativeTargetChartAttachment.M P w)
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P (p ≫ q) w)
    (CoefficientBassRaw1PolynomialPostcomp.reference P p q w)
    (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d))
    (G ≫ CoefficientBassNegativeTargetChartAttachment.L P w)
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P w D G ε)
    (CoefficientBassRaw1PolynomialCompositeEndpoint.polynomialIso P (p ≫ q) w)
    (CoefficientBassRaw1PolynomialRadialCaps.leftPolynomialIso P p q w)
    (CoefficientBassNegativeTargetSingleSheet.firstMap P w D G ε z)
  rw [polynomial_word] at hn
  have ha := Negative.action_normalization P w D
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassRaw1PolynomialPostcomp.reference P p q w) G ε
    (CoefficientBassRaw1PolynomialPairDirectAction.polynomialIso P p q)
    (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w) z
  exact hn.trans ha

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPostcompRadialEndpoint
