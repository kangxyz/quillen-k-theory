/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPostcompInputSecondCell
/-! The complete final postcomposition and input-cap seam in the fixed polynomial triple. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPostcompInputEndpoint
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier BassH0Merge BassH1Join
open CoefficientBassRaw1PolynomialTripleAnchor BassReferenceMerge

private theorem triple_word {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    NormalizedTripleSimplex.leftFirst f g h ≪≫
      isoWhiskerRight (BinaryNormalizationSimplex.total g h) (normalizedMap f).functor =
    NormalizedTripleSimplex.rightFirst f g h ≪≫
      isoWhiskerLeft (normalizedMap h).functor (BinaryNormalizationSimplex.total f g) := by
  have hl : NormalizedTripleSimplex.leftSecond f g h =
      isoWhiskerRight (BinaryNormalizationSimplex.total g h) (normalizedMap f).functor := by
    have ha : Functor.associator (boundedFlatNormalizedPullback h)
        (boundedFlatNormalizedPullback g) (boundedFlatNormalizedPullback f) = Iso.refl _ := rfl
    change smallIso (isoWhiskerRight (boundedFlatNormalizedPullbackCompIso g h)
      (boundedFlatNormalizedPullback f) ≪≫ _) = _
    rw [ha, Iso.trans_refl]
    exact (smallIso_postcomp (boundedFlatNormalizedPullbackCompIso g h)
      (boundedFlatNormalizedPullback f)).symm
  have hr : NormalizedTripleSimplex.rightSecond f g h =
      isoWhiskerLeft (normalizedMap h).functor (BinaryNormalizationSimplex.total f g) := by
    exact (smallIso_precomp (boundedFlatNormalizedPullback h)
      (boundedFlatNormalizedPullbackCompIso f g)).symm
  apply Iso.ext
  simpa only [Iso.trans_hom, ← hl, ← hr] using NormalizedTripleSimplex.two_routes f g h

private theorem binary_terminal {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    binaryNodes f g 2 =
      (⟨normalizedMap g ≫ normalizedMap f, BinaryNormalizationSimplex.total f g⟩ :
        Node (BinaryNormalizationSimplex.sourceMap f g)) := by rfl

private theorem triple_node {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) :
    CommonReferenceProduct.reanchor (NormalizedTripleSimplex.leftFirst f g h)
      (postcompNode (normalizedMap f) (binaryNodes g h 2)) =
    CommonReferenceProduct.reanchor (NormalizedTripleSimplex.rightFirst f g h)
      (precompNode (normalizedMap h) (binaryNodes f g 2)) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  exact triple_word f g h

private theorem moving_as_pre {V W T : Model.{v}} (D : V ⟶ W) (H : W ⟶ T)
    (G : V ⟶ T) (η : G.functor ≅ (D ≫ H).functor) (N : Node D) (Z : Node H) :
    (⟨N.1 ≫ Z.1, η ≪≫ isoWhiskerLeft D.functor Z.2 ≪≫
      isoWhiskerRight N.2 Z.1.functor⟩ : Node G) =
    preReferenceNode G N.1 (η ≪≫ isoWhiskerRight N.2 H.functor) Z := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  apply Iso.ext
  ext X
  have h := Z.2.hom.naturality (N.2.hom.app X)
  have hh := congrArg (fun k ↦ η.hom.app X ≫ k) h
  simpa only [preReferenceNode, Iso.trans_hom, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, NatTrans.comp_app, whiskerLeft_app, whiskerRight_app,
    Category.assoc] using hh.symm

private theorem binary_moving_as_pre {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {T : Model.{u + 1}} (H : modelOf (boundedFlatPerfectWaldhausen X) ⟶ T)
    (G : modelOf (boundedFlatPerfectWaldhausen Z) ⟶ T)
    (η : G.functor ≅ (BinaryNormalizationSimplex.sourceMap f g ≫ H).functor)
    (N : Node H) :
    (⟨(binaryNodes f g 2).1 ≫ N.1, η ≪≫
      isoWhiskerLeft (BinaryNormalizationSimplex.sourceMap f g).functor N.2 ≪≫
      isoWhiskerRight (binaryNodes f g 2).2 N.1.functor⟩ : Node G) =
    preReferenceNode G (normalizedMap g ≫ normalizedMap f)
      (η ≪≫ isoWhiskerRight (BinaryNormalizationSimplex.total f g) H.functor) N := by
  exact moving_as_pre _ _ _ _ (binaryNodes f g 2) N

private theorem precomp_cylinder {U V W T : Model.{v}}
    (A : U ⟶ V) (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
    (ε : G.functor ≅ (F ≫ J).functor) (y : |parameterSSet F|) (t : I) :
    CutOpenPrecomp.firstMap A F J G ε
      (DoubleCylinder.realizedCylinder (attaching F J G ε) (erase F) (y, ULift.up t)) =
    DoubleCylinder.realizedCylinder
      (attaching (A ≫ F) J (A ≫ G) (CutOpenPrecomp.anchor A F J G ε)) (erase (A ≫ F))
      (mapParameter (precompNode A) y, ULift.up t) :=
  DoubleCylinder.map_cylinder_apply
    (first_isPushout F J G ε)
    (first_isPushout (A ≫ F) J (A ≫ G) (CutOpenPrecomp.anchor A F J G ε))
    (CutOpenPrecomp.parameterMap A F) (CutOpenPrecomp.parameterMap A G) (𝟙 _)
    (CutOpenPrecomp.attachment_square A F J G ε) (CutOpenPrecomp.erase_square A F)
    y (ULift.up t)

private theorem normalized_pre_attach {U V W T : Model.{v}}
    (A : U ⟶ V) (F : V ⟶ W) (K : U ⟶ W) (J : W ⟶ T)
    (δ : K.functor ≅ (A ≫ F).functor) (N : Node F) :
    CommonReferenceProduct.reanchor
      (CoefficientBassPolynomialSheetNormalization.laurentIso (A ≫ F) K J (A ≫ (F ≫ J))
        (CutOpenPrecomp.anchor A F J (F ≫ J) (Iso.refl _)) δ)
      (precompNode A (postcompNode J N)) =
      postcompNode J (CommonReferenceProduct.reanchor δ (precompNode A N)) := by
  have h := congrArg (CommonReferenceProduct.reanchor
    (CoefficientBassPolynomialSheetNormalization.laurentIso (A ≫ F) K J (A ≫ (F ≫ J))
      (CutOpenPrecomp.anchor A F J (F ≫ J) (Iso.refl _)) δ))
    (CutOpenPrecomp.attachment_node A F J (F ≫ J) (Iso.refl _) N)
  have hn := CoefficientBassPolynomialSheetNormalization.attachment_node (A ≫ F) K J
    (A ≫ (F ≫ J)) (CutOpenPrecomp.anchor A F J (F ≫ J) (Iso.refl _)) δ
    (precompNode A N)
  simpa only [attachPostcompNode, postcompNode, Iso.refl_trans] using h.trans hn

private theorem finite_parameter_node {V W T : Model.{v}}
    (E : V ⟶ W) (F : V ⟶ T) {k : ℕ} (f : Node E → Fin (k + 1) → Node F)
    (e : Node E) (z : StdSimplex ℝ (Fin (k + 1))) :
    FiniteParameter.parameter E F f
      (parameter E (fun _ : Fin 1 ↦ e) (StdSimplex.single 0), z) =
      parameter F (f e) z := by
  rw [FiniteParameter.parameter_characteristic, SimplexGrid.parameter_row, parameter_face]
  apply congrArg (fun N ↦ parameter F N z)
  funext j
  exact FiniteParameter.gridNodes_index E F f (fun _ : Fin 1 ↦ e) 0 j

private theorem map_two_parameter {V₀ W₀ V₁ W₁ V₂ W₂ : Model.{v}}
    {F₀ : V₀ ⟶ W₀} {F₁ : V₁ ⟶ W₁} {F₂ : V₂ ⟶ W₂}
    (g : Node F₀ → Node F₁) (h : Node F₁ → Node F₂)
    {k : ℕ} (N : Fin (k + 1) → Node F₀) (z : StdSimplex ℝ (Fin (k + 1))) :
    mapParameter h (mapParameter g (parameter F₀ N z)) =
    parameter F₂ (fun i ↦ h (g (N i))) z := by
  rw [mapParameter_parameter, mapParameter_parameter]

private theorem finite_map_node_parameter {V W T U : Model.{v}}
    (E : V ⟶ W) (F : V ⟶ T) (G : V ⟶ U) {k : ℕ}
    (f : Node E → Fin (k + 1) → Node F) (e : Node E)
    (z : StdSimplex ℝ (Fin (k + 1))) (g : Node F → Node G) :
    mapParameter g (FiniteParameter.parameter E F f
      (parameter E (fun _ : Fin 1 ↦ e) (StdSimplex.single 0), z)) =
      parameter G (fun i ↦ g (f e i)) z := by
  rw [finite_parameter_node, mapParameter_parameter]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The full terminal binary node lies on the original polynomial attaching face. -/
theorem second_terminal :
    CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes P β p q 4 =
      postcompNode (BassMWholeNerve.coefficientModel P (β.app c))
        (binaryNodes (polynomialArrow P q) (polynomialArrow P p) 2) := by
  rw [← CoefficientBassRaw1PolynomialPairEndpointReferences.second_nodes]
  exact CoefficientBassRaw1PolynomialSourceAttachment.sheet_source_nodes P β p q 2

/-- The two original polynomial normalization routes agree as complete dependent nodes. -/
theorem polynomial_node :
    CommonReferenceProduct.reanchor (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w)
      (postcompNode (normalizedMap (polynomialArrow P w))
        (binaryNodes (polynomialArrow P q) (polynomialArrow P p) 2)) =
    CommonReferenceProduct.reanchor (CoefficientBassRaw1PolynomialInputCap.polynomialIso P p q w)
      (precompNode (normalizedMap (polynomialArrow P p))
        (binaryNodes (polynomialArrow P w) (polynomialArrow P q) 2)) := by
  exact triple_node (polynomialArrow P w) (polynomialArrow P q) (polynomialArrow P p)

private theorem paused_endpoint :
    CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1 =
    parameter (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
      (fun _ : Fin 1 ↦ binaryNodes (polynomialArrow P q) (polynomialArrow P p) 2)
      (StdSimplex.single 0) := by
  change parameter _ _
    (CoefficientBassRaw1PolynomialSourceAttachment.pausedBinaryParameter 1) = _
  rw [Path.target]
  simpa only [StdSimplex.map_single, SimplexCategory.const_apply] using
    parameter_face (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
      (binaryNodes (polynomialArrow P q) (polynomialArrow P p))
      (SimplexCategory.const ⦋0⦌ ⦋2⦌ 2) (StdSimplex.single 0)

/-- The complete polynomial endpoint is the same whole nerve point in the fixed triple. -/
theorem polynomial_parameter :
    mapParameter (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w))
      (mapParameter (postcompNode (normalizedMap (polynomialArrow P w)))
        (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1)) =
    mapParameter (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialInputCap.polynomialIso P p q w))
      (mapParameter (precompNode (normalizedMap (polynomialArrow P p)))
        (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P q w 1)) := by
  rw [paused_endpoint, paused_endpoint]
  have hl := map_two_parameter
    (postcompNode (normalizedMap (polynomialArrow P w)))
    (CommonReferenceProduct.reanchor (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w))
    (fun _ : Fin 1 ↦ binaryNodes (polynomialArrow P q) (polynomialArrow P p) 2)
    (StdSimplex.single 0)
  have hr := map_two_parameter
    (precompNode (CoefficientBassRaw1ChartCompositionProduct.polynomialInput P p))
    (CommonReferenceProduct.reanchor (CoefficientBassRaw1PolynomialInputCap.polynomialIso P p q w))
    (fun _ : Fin 1 ↦ binaryNodes (polynomialArrow P w) (polynomialArrow P q) 2)
    (StdSimplex.single 0)
  exact hl.trans ((congrArg (fun N ↦ parameter (polynomialReference P p q w) N
    (StdSimplex.single 0)) (funext (fun _ : Fin 1 ↦ polynomial_node P p q w))).trans hr.symm)


private theorem input_precomp_cylinder
    (y : |parameterSSet (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P q w)|)
    (t : I) :
    CoefficientBassRaw1PolynomialInputCap.place P β p q w
      (CoefficientBassRaw1PolynomialInputCap.precomp P β p q w
        (CoefficientBassRaw1PolynomialPairCone.cylinder P β q w (y, t))) =
    DoubleCylinder.realizedCylinder
      (attaching (polynomialReference P p q w) (normalizedMap (chart P β d))
        (polynomialReference P p q w ≫ normalizedMap (chart P β d)) (Iso.refl _))
      (erase (polynomialReference P p q w))
      (mapParameter (CommonReferenceProduct.reanchor
        (CoefficientBassRaw1PolynomialInputCap.polynomialIso P p q w))
        (mapParameter (precompNode (normalizedMap (polynomialArrow P p))) y), ULift.up t) := by
  have h : CoefficientBassRaw1PolynomialInputCap.precomp P β p q w
        (CoefficientBassRaw1PolynomialPairCone.cylinder P β q w (y, t)) =
      DoubleCylinder.realizedCylinder
        (attaching
          (CoefficientBassRaw1ChartCompositionProduct.polynomialInput P p ≫
            CoefficientBassRaw1PolynomialPausedChart.polynomialReference P q w)
          (normalizedMap (chart P β d))
          (CoefficientBassRaw1ChartCompositionProduct.polynomialInput P p ≫
            CoefficientBassRaw1PolynomialPausedChart.sheetReference P β q w)
          (CutOpenPrecomp.anchor _ _ _ _ (Iso.refl _)))
        (erase (CoefficientBassRaw1ChartCompositionProduct.polynomialInput P p ≫
          CoefficientBassRaw1PolynomialPausedChart.polynomialReference P q w))
        (mapParameter (precompNode (normalizedMap (polynomialArrow P p))) y, ULift.up t) :=
    precomp_cylinder _ _ _ _ _ y t
  exact (congrArg (CoefficientBassRaw1PolynomialInputCap.place P β p q w) h).trans
    (CoefficientBassPolynomialSheetNormalization.map_cylinder _ _ _ _ _ _ _ _)

/-- The third input row retains source precomposition and its full placement reference. -/
def inputThirdNodes (i : Fin 5) :
    Node (polynomialReference P p q w ≫ normalizedMap (chart P β d)) :=
  CommonReferenceProduct.reanchor (inputLowerIso P β p q w)
    (precompNode (normalizedMap (polynomialArrow P p))
      (CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes P β q w i))

private theorem input_third_terminal : inputThirdNodes P β p q w 4 =
    postcompNode (normalizedMap (chart P β d))
      (CommonReferenceProduct.reanchor (CoefficientBassRaw1PolynomialInputCap.polynomialIso P p q w)
        (precompNode (normalizedMap (polynomialArrow P p))
          (binaryNodes (polynomialArrow P w) (polynomialArrow P q) 2))) := by
  rw [inputThirdNodes, second_terminal]
  exact normalized_pre_attach _ _ _ _ _ _

/-- The complete last plus chart row under the actual postcomposition map. -/
def plusThirdNodes (i : Fin 5) :
    Node (polynomialReference P p q w ≫ normalizedMap (chart P (underToLaurent R) d)) :=
  CommonReferenceProduct.reanchor (postcompLowerIso P (underToLaurent R) p q w)
    (CoefficientBassSeedTargetChartAttachment.movingNode P w
      (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
      (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
      (Iso.refl _) (binaryNodes (polynomialArrow P q) (polynomialArrow P p) 2) i)

private theorem plus_third_terminal : plusThirdNodes P p q w 4 =
    inputThirdNodes P (underToLaurent R) p q w 4 := by
  rw [plusThirdNodes, CoefficientBassSeedTargetChartAttachment.movingNode_one,
    ← plus_lower_iso]
  erw [CoefficientBassPolynomialSheetNormalization.attachment_node]
  rw [input_third_terminal]
  change postcompNode _ (CommonReferenceProduct.reanchor _ (postcompNode _ _)) = _
  exact congrArg (postcompNode _) (polynomial_node P p q w)

/-- All five original plus chart nodes agree before realization. -/
theorem plus_third_nodes (i : Fin 5) : plusThirdNodes P p q w i =
    inputThirdNodes P (underToLaurent R) p q w i := by
  apply pre_families_match
    (polynomialReference P p q w ≫ normalizedMap (chart P (underToLaurent R) d))
    (normalizedMap (polynomialArrow P p) ≫ normalizedMap (polynomialArrow P q))
    (CoefficientBassSeedTargetChartAttachment.H P w)
    (NativeSquareFiveSimplex.nodes (laurentArrow P w) (chart P (underToLaurent R) c)
      (chart P (underToLaurent R) d) (polynomialArrow P w)
      (coefficientMap_naturality P (underToLaurent R) w))
    (ρ := (postcompLowerIso P (underToLaurent R) p q w ≪≫
      CoefficientBassSeedTargetChartAttachment.squareAnchor P w
        (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
        (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
        (Iso.refl _)) ≪≫ isoWhiskerRight
          (BinaryNormalizationSimplex.total (polynomialArrow P q) (polynomialArrow P p))
          (CoefficientBassSeedTargetChartAttachment.H P w).functor)
    («σ» := inputLowerIso P (underToLaurent R) p q w ≪≫
      isoWhiskerLeft (normalizedMap (polynomialArrow P p)).functor
        (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P (underToLaurent R) q w ≪≫
          CoefficientMovingSquareRows.secondAnchor
            (polynomialArrow P q) (polynomialArrow P w) (laurentArrow P w)
            (chart P (underToLaurent R) c) (chart P (underToLaurent R) d)
            (coefficientMap_naturality P (underToLaurent R) w).symm))
    ?_ ?_ 4 (plus_third_terminal P p q w) i
  · intro j
    dsimp only [plusThirdNodes, CommonReferenceProduct.reanchor,
      CoefficientBassSeedTargetChartAttachment.movingNode]
    have h := binary_moving_as_pre (polynomialArrow P q) (polynomialArrow P p)
      (CoefficientBassSeedTargetChartAttachment.H P w)
      (polynomialReference P p q w ≫ normalizedMap (chart P (underToLaurent R) d))
      (postcompLowerIso P (underToLaurent R) p q w ≪≫
        CoefficientBassSeedTargetChartAttachment.squareAnchor P w
          (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
          (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
            (Iso.refl _))
      (NativeSquareFiveSimplex.nodes (laurentArrow P w) (chart P (underToLaurent R) c)
        (chart P (underToLaurent R) d) (polynomialArrow P w)
        (coefficientMap_naturality P (underToLaurent R) w) j)
    dsimp only [polynomialArrow, laurentArrow, chart, laurentPlus] at h ⊢
    simpa only [Iso.trans_assoc] using h
  · intro j
    simp only [inputThirdNodes, CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes,
      CommonReferenceProduct.reanchor, precompNode, preReferenceNode,
      isoWhiskerLeft_trans, Iso.trans_assoc]
    rfl

/-- The complete last minus chart row under the actual postcomposition map. -/
def minusThirdNodes (i : Fin 5) :
    Node (polynomialReference P p q w ≫ normalizedMap (chart P (underToLaurentInvert R) d)) :=
  CommonReferenceProduct.reanchor (postcompLowerIso P (underToLaurentInvert R) p q w)
    (CoefficientBassNegativeTargetChartAttachment.movingNode P w
      (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
      (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R) p q)
      (Iso.refl _) (binaryNodes (polynomialArrow P q) (polynomialArrow P p) 2) i)

private theorem minus_third_terminal : minusThirdNodes P p q w 4 =
    inputThirdNodes P (underToLaurentInvert R) p q w 4 := by
  rw [minusThirdNodes, CoefficientBassNegativeTargetChartAttachment.movingNode_one,
    ← minus_lower_iso]
  erw [CoefficientBassPolynomialSheetNormalization.attachment_node]
  rw [input_third_terminal]
  change postcompNode _ (CommonReferenceProduct.reanchor _ (postcompNode _ _)) = _
  exact congrArg (postcompNode _) (polynomial_node P p q w)

/-- All five original minus chart nodes agree before realization. -/
theorem minus_third_nodes (i : Fin 5) : minusThirdNodes P p q w i =
    inputThirdNodes P (underToLaurentInvert R) p q w i := by
  apply pre_families_match
    (polynomialReference P p q w ≫ normalizedMap (chart P (underToLaurentInvert R) d))
    (normalizedMap (polynomialArrow P p) ≫ normalizedMap (polynomialArrow P q))
    (CoefficientBassNegativeTargetChartAttachment.H P w)
    (NativeSquareFiveSimplex.nodes (laurentArrow P w) (chart P (underToLaurentInvert R) c)
      (chart P (underToLaurentInvert R) d) (polynomialArrow P w)
      (coefficientMap_naturality P (underToLaurentInvert R) w))
    (ρ := (postcompLowerIso P (underToLaurentInvert R) p q w ≪≫
      CoefficientBassNegativeTargetChartAttachment.squareAnchor P w
        (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
        (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R) p q)
        (Iso.refl _)) ≪≫ isoWhiskerRight
          (BinaryNormalizationSimplex.total (polynomialArrow P q) (polynomialArrow P p))
          (CoefficientBassNegativeTargetChartAttachment.H P w).functor)
    («σ» := inputLowerIso P (underToLaurentInvert R) p q w ≪≫
      isoWhiskerLeft (normalizedMap (polynomialArrow P p)).functor
        (CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P (underToLaurentInvert R) q w ≪≫
          CoefficientMovingSquareRows.secondAnchor
            (polynomialArrow P q) (polynomialArrow P w) (laurentArrow P w)
            (chart P (underToLaurentInvert R) c) (chart P (underToLaurentInvert R) d)
            (coefficientMap_naturality P (underToLaurentInvert R) w).symm))
    ?_ ?_ 4 (minus_third_terminal P p q w) i
  · intro j
    dsimp only [minusThirdNodes, CommonReferenceProduct.reanchor,
      CoefficientBassNegativeTargetChartAttachment.movingNode]
    have h := binary_moving_as_pre (polynomialArrow P q) (polynomialArrow P p)
      (CoefficientBassNegativeTargetChartAttachment.H P w)
      (polynomialReference P p q w ≫ normalizedMap (chart P (underToLaurentInvert R) d))
      (postcompLowerIso P (underToLaurentInvert R) p q w ≪≫
        CoefficientBassNegativeTargetChartAttachment.squareAnchor P w
          (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
          (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R) p q)
            (Iso.refl _))
      (NativeSquareFiveSimplex.nodes (laurentArrow P w) (chart P (underToLaurentInvert R) c)
        (chart P (underToLaurentInvert R) d) (polynomialArrow P w)
        (coefficientMap_naturality P (underToLaurentInvert R) w) j)
    dsimp only [polynomialArrow, laurentArrow, chart, laurentMinus] at h ⊢
    simpa only [Iso.trans_assoc] using h
  · intro j
    simp only [inputThirdNodes, CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes,
      CommonReferenceProduct.reanchor, precompNode, preReferenceNode,
      isoWhiskerLeft_trans, Iso.trans_assoc]
    rfl

private theorem plus_third_family (t : I) :
    mapParameter (CommonReferenceProduct.reanchor (postcompLowerIso P (underToLaurent R) p q w))
      (CoefficientBassSeedTargetChartAttachment.moving P w
        (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
        (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q)
          (Iso.refl _)
        (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1, t)) =
    mapParameter (CommonReferenceProduct.reanchor (inputLowerIso P (underToLaurent R) p q w))
      (mapParameter (precompNode (normalizedMap (polynomialArrow P p)))
        (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) q
          w)
          (CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes P (underToLaurent R) q w)
          (NativeSquareFiveSimplex.parameter t))) := by
  rw [paused_endpoint]
  dsimp only [CoefficientBassSeedTargetChartAttachment.moving,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  have hl := finite_map_node_parameter
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q ≫
      CoefficientBassSeedTargetChartAttachment.L P w)
    (polynomialReference P p q w ≫ normalizedMap (chart P (underToLaurent R) d))
    (CoefficientBassSeedTargetChartAttachment.movingNode P w
      (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
      (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurent R) p q) (Iso.refl
        _))
    (binaryNodes (polynomialArrow P q) (polynomialArrow P p) 2)
    (NativeSquareFiveSimplex.parameter t)
    (CommonReferenceProduct.reanchor (postcompLowerIso P (underToLaurent R) p q w))
  have hr := map_two_parameter
    (precompNode (CoefficientBassRaw1ChartCompositionProduct.polynomialInput P p))
    (CommonReferenceProduct.reanchor (inputLowerIso P (underToLaurent R) p q w))
    (CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes P (underToLaurent R) q w)
    (NativeSquareFiveSimplex.parameter t)
  exact hl.trans ((congrArg (fun N ↦ parameter
    (polynomialReference P p q w ≫ normalizedMap (chart P (underToLaurent R) d)) N
    (NativeSquareFiveSimplex.parameter t)) (funext (plus_third_nodes P p q w))).trans hr.symm)

private theorem minus_third_family (t : I) :
    mapParameter (CommonReferenceProduct.reanchor (postcompLowerIso P (underToLaurentInvert R) p q
      w))
      (CoefficientBassNegativeTargetChartAttachment.moving P w
        (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
        (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R) p q)
          (Iso.refl _)
        (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1, t)) =
    mapParameter (CommonReferenceProduct.reanchor (inputLowerIso P (underToLaurentInvert R) p q w))
      (mapParameter (precompNode (normalizedMap (polynomialArrow P p)))
        (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P
          (underToLaurentInvert R) q w)
          (CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes P (underToLaurentInvert
            R) q w)
          (NativeSquareFiveSimplex.parameter t))) := by
  rw [paused_endpoint]
  dsimp only [CoefficientBassNegativeTargetChartAttachment.moving,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk]
  have hl := finite_map_node_parameter
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R) p q ≫
      CoefficientBassNegativeTargetChartAttachment.L P w)
    (polynomialReference P p q w ≫ normalizedMap (chart P (underToLaurentInvert R) d))
    (CoefficientBassNegativeTargetChartAttachment.movingNode P w
      (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q)
      (CoefficientBassRaw1PolynomialPausedChart.sheetReference P (underToLaurentInvert R) p q)
        (Iso.refl _))
    (binaryNodes (polynomialArrow P q) (polynomialArrow P p) 2)
    (NativeSquareFiveSimplex.parameter t)
    (CommonReferenceProduct.reanchor (postcompLowerIso P (underToLaurentInvert R) p q w))
  have hr := map_two_parameter
    (precompNode (CoefficientBassRaw1ChartCompositionProduct.polynomialInput P p))
    (CommonReferenceProduct.reanchor (inputLowerIso P (underToLaurentInvert R) p q w))
    (CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes P (underToLaurentInvert R) q w)
    (NativeSquareFiveSimplex.parameter t)
  exact hl.trans ((congrArg (fun N ↦ parameter
    (polynomialReference P p q w ≫ normalizedMap (chart P (underToLaurentInvert R) d)) N
    (NativeSquareFiveSimplex.parameter t)) (funext (minus_third_nodes P p q w))).trans hr.symm)

/-- The actual plus third cell retains its literal nested half clock. -/
theorem plus_third_cell (t : I) :
    CoefficientBassRaw1PolynomialPostcomp.plus P p q w
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurent R) p q
        (1, upper (upper (lower t)))) =
    CoefficientBassRaw1PolynomialInputCap.place P (underToLaurent R) p q w
      (CoefficientBassRaw1PolynomialInputCap.last P (underToLaurent R) p q w
        (1, upper (lower t))) := by
  rw [← CoefficientBassRaw1PolynomialCompositeEndpoint.plusPath_corrected_one,
    CoefficientBassRaw1PolynomialCompositeEndpoint.plusPath_third]
  dsimp only [CoefficientBassRaw1PolynomialInputCap.last, ContinuousMap.comp_apply]
  rw [← CoefficientBassRaw1PolynomialCompositeEndpoint.plusPath_corrected_one,
    CoefficientBassRaw1PolynomialCompositeEndpoint.plusPath_second]
  rw [CoefficientBassRaw1PolynomialPostcompInputSecondCell.input_precomp_laurent]
  let κ := CoefficientBassPolynomialSheetNormalization.map
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫ CoefficientBassSeedTargetChartAttachment.M
      P w)
    (polynomialReference P p q w) (CoefficientBassSeedTargetChartAttachment.Jb P (b := d))
    ((CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) ≫
      CoefficientBassSeedTargetChartAttachment.L P w)
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _))
    (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w)
  have hc := CoefficientBassPositiveTargetSingleSheet.firstMap_cylinder P w
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _)
    (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1) (lower t)
  have ht := ScalarRectangle.homotopy_lower
    (CoefficientBassPositiveTargetSingleSheet.chartTrack P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _) false)
    (CoefficientBassPositiveTargetSingleSheet.contraction P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _) false)
    t (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1)
  have h := congrArg κ (hc.trans ht)
  have hn := CoefficientBassPolynomialSheetNormalization.map_laurent
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫ CoefficientBassSeedTargetChartAttachment.M
      P w)
    (polynomialReference P p q w) (CoefficientBassSeedTargetChartAttachment.Jb P (b := d))
    ((CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) ≫
      CoefficientBassSeedTargetChartAttachment.L P w)
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _))
    (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w)
    (CoefficientBassSeedTargetChartAttachment.moving P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _)
      (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1, t))
  rw [plus_lower_iso] at hn
  exact h.trans (hn.trans (congrArg _ (plus_third_family P p q w t)))

/-- The actual plus fourth cell retains its literal nested half clock. -/
theorem plus_fourth_cell (t : I) :
    CoefficientBassRaw1PolynomialPostcomp.plus P p q w
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurent R) p q
        (1, upper (upper (upper t)))) =
    CoefficientBassRaw1PolynomialInputCap.place P (underToLaurent R) p q w
      (CoefficientBassRaw1PolynomialInputCap.last P (underToLaurent R) p q w
        (1, upper (upper t))) := by
  rw [← CoefficientBassRaw1PolynomialCompositeEndpoint.plusPath_corrected_one,
    CoefficientBassRaw1PolynomialCompositeEndpoint.plusPath_third]
  dsimp only [CoefficientBassRaw1PolynomialInputCap.last, ContinuousMap.comp_apply]
  rw [← CoefficientBassRaw1PolynomialCompositeEndpoint.plusPath_corrected_one,
    CoefficientBassRaw1PolynomialCompositeEndpoint.plusPath_third]
  rw [input_precomp_cylinder]
  let κ := CoefficientBassPolynomialSheetNormalization.map
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫ CoefficientBassSeedTargetChartAttachment.M
      P w)
    (polynomialReference P p q w) (CoefficientBassSeedTargetChartAttachment.Jb P (b := d))
    ((CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) ≫
      CoefficientBassSeedTargetChartAttachment.L P w)
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _))
    (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w)
  have hc := CoefficientBassPositiveTargetSingleSheet.firstMap_cylinder P w
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _)
    (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1) (upper t)
  have ht := ScalarRectangle.homotopy_upper
    (CoefficientBassPositiveTargetSingleSheet.chartTrack P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _) false)
    (CoefficientBassPositiveTargetSingleSheet.contraction P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _) false)
    t (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1)
  have h := congrArg κ (hc.trans ht)
  have hn := CoefficientBassPolynomialSheetNormalization.map_cylinder
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫ CoefficientBassSeedTargetChartAttachment.M
      P w)
    (polynomialReference P p q w) (CoefficientBassSeedTargetChartAttachment.Jb P (b := d))
    ((CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) ≫
      CoefficientBassSeedTargetChartAttachment.L P w)
    (CoefficientBassSeedTargetChartAttachment.targetAnchor P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassSeedTargetChartAttachment.Ja P (a := c)) (Iso.refl _))
    (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w)
    (CoefficientBassPositiveTargetSingleSheet.polynomialMap P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1)) t
  exact h.trans (hn.trans (congrArg
    (fun y ↦ DoubleCylinder.realizedCylinder
      (attaching (polynomialReference P p q w) (normalizedMap (chart P (underToLaurent R) d))
        (polynomialReference P p q w ≫ normalizedMap (chart P (underToLaurent R) d)) (Iso.refl _))
      (erase (polynomialReference P p q w)) (y, ULift.up t))
    (polynomial_parameter P p q w)))

/-- The actual minus third cell retains its literal nested half clock. -/
theorem minus_third_cell (t : I) :
    CoefficientBassRaw1PolynomialPostcomp.minus P p q w
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurentInvert R) p q
        (1, upper (upper (lower t)))) =
    CoefficientBassRaw1PolynomialInputCap.place P (underToLaurentInvert R) p q w
      (CoefficientBassRaw1PolynomialInputCap.last P (underToLaurentInvert R) p q w
        (1, upper (lower t))) := by
  rw [← CoefficientBassRaw1PolynomialCompositeEndpoint.minusPath_corrected_one,
    CoefficientBassRaw1PolynomialCompositeEndpoint.minusPath_third]
  dsimp only [CoefficientBassRaw1PolynomialInputCap.last, ContinuousMap.comp_apply]
  rw [← CoefficientBassRaw1PolynomialCompositeEndpoint.minusPath_corrected_one,
    CoefficientBassRaw1PolynomialCompositeEndpoint.minusPath_second]
  rw [CoefficientBassRaw1PolynomialPostcompInputSecondCell.input_precomp_laurent]
  let κ := CoefficientBassPolynomialSheetNormalization.map
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassNegativeTargetChartAttachment.M P w)
    (polynomialReference P p q w) (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d))
    ((CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) ≫
      CoefficientBassNegativeTargetChartAttachment.L P w)
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _))
    (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w)
  have hc := CoefficientBassNegativeTargetSingleSheet.firstMap_cylinder P w
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _)
    (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1) (lower t)
  have ht := ScalarRectangle.homotopy_lower
    (CoefficientBassNegativeTargetSingleSheet.chartTrack P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _) false)
    (CoefficientBassNegativeTargetSingleSheet.contraction P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _) false)
    t (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1)
  have h := congrArg κ (hc.trans ht)
  have hn := CoefficientBassPolynomialSheetNormalization.map_laurent
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassNegativeTargetChartAttachment.M P w)
    (polynomialReference P p q w) (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d))
    ((CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) ≫
      CoefficientBassNegativeTargetChartAttachment.L P w)
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _))
    (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w)
    (CoefficientBassNegativeTargetChartAttachment.moving P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _)
      (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1, t))
  rw [minus_lower_iso] at hn
  exact h.trans (hn.trans (congrArg _ (minus_third_family P p q w t)))

/-- The actual minus fourth cell retains its literal nested half clock. -/
theorem minus_fourth_cell (t : I) :
    CoefficientBassRaw1PolynomialPostcomp.minus P p q w
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurentInvert R) p q
        (1, upper (upper (upper t)))) =
    CoefficientBassRaw1PolynomialInputCap.place P (underToLaurentInvert R) p q w
      (CoefficientBassRaw1PolynomialInputCap.last P (underToLaurentInvert R) p q w
        (1, upper (upper t))) := by
  rw [← CoefficientBassRaw1PolynomialCompositeEndpoint.minusPath_corrected_one,
    CoefficientBassRaw1PolynomialCompositeEndpoint.minusPath_third]
  dsimp only [CoefficientBassRaw1PolynomialInputCap.last, ContinuousMap.comp_apply]
  rw [← CoefficientBassRaw1PolynomialCompositeEndpoint.minusPath_corrected_one,
    CoefficientBassRaw1PolynomialCompositeEndpoint.minusPath_third]
  rw [input_precomp_cylinder]
  let κ := CoefficientBassPolynomialSheetNormalization.map
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassNegativeTargetChartAttachment.M P w)
    (polynomialReference P p q w) (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d))
    ((CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) ≫
      CoefficientBassNegativeTargetChartAttachment.L P w)
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _))
    (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w)
  have hc := CoefficientBassNegativeTargetSingleSheet.firstMap_cylinder P w
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _)
    (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1) (upper t)
  have ht := ScalarRectangle.homotopy_upper
    (CoefficientBassNegativeTargetSingleSheet.chartTrack P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _) false)
    (CoefficientBassNegativeTargetSingleSheet.contraction P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _) false)
    t (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1)
  have h := congrArg κ (hc.trans ht)
  have hn := CoefficientBassPolynomialSheetNormalization.map_cylinder
    (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassNegativeTargetChartAttachment.M P w)
    (polynomialReference P p q w) (CoefficientBassNegativeTargetChartAttachment.Jb P (b := d))
    ((CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
      CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) ≫
      CoefficientBassNegativeTargetChartAttachment.L P w)
    (CoefficientBassNegativeTargetChartAttachment.targetAnchor P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q ≫
        CoefficientBassNegativeTargetChartAttachment.Ja P (a := c)) (Iso.refl _))
    (CoefficientBassRaw1PolynomialPostcomp.polynomialIso P p q w)
    (CoefficientBassNegativeTargetSingleSheet.polynomialMap P w
      (CoefficientBassRaw1PolynomialPostcomp.pair P p q)
      (CoefficientBassRaw1PolynomialSourceAttachment.polynomialPausedPath P p q 1)) t
  exact h.trans (hn.trans (congrArg
    (fun y ↦ DoubleCylinder.realizedCylinder
      (attaching (polynomialReference P p q w) (normalizedMap (chart P (underToLaurentInvert R) d))
        (polynomialReference P p q w ≫ normalizedMap (chart P (underToLaurentInvert R) d))
          (Iso.refl _))
      (erase (polynomialReference P p q w)) (y, ULift.up t))
    (polynomial_parameter P p q w)))

private theorem placed_lower (t : I) :
    CoefficientBassRaw1PolynomialInputCap.placedFamily P β p q w (1, lower t) =
    CoefficientBassRaw1PolynomialInputCap.place P β p q w
      (CoefficientBassRaw1PolynomialInputCap.first P β p q w (1, t)) :=
  congrArg (CoefficientBassRaw1PolynomialInputCap.place P β p q w)
    (ScalarRectangle.homotopy_lower
      (CoefficientBassRaw1PolynomialInputCap.firstSwap P β p q w)
      (CoefficientBassRaw1PolynomialInputCap.lastSwap P β p q w) t 1)

private theorem placed_upper (t : I) :
    CoefficientBassRaw1PolynomialInputCap.placedFamily P β p q w (1, upper t) =
    CoefficientBassRaw1PolynomialInputCap.place P β p q w
      (CoefficientBassRaw1PolynomialInputCap.last P β p q w (1, t)) :=
  congrArg (CoefficientBassRaw1PolynomialInputCap.place P β p q w)
    (ScalarRectangle.homotopy_upper
      (CoefficientBassRaw1PolynomialInputCap.firstSwap P β p q w)
      (CoefficientBassRaw1PolynomialInputCap.lastSwap P β p q w) t 1)

/-- The whole final plus edge is an equality in the unchanged actual polynomial triple sheet. -/
theorem plus_endpoint (s : I) :
    CoefficientBassRaw1PolynomialPostcomp.plus P p q w
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurent R) p q (1, s)) =
    CoefficientBassRaw1PolynomialInputCap.placedFamily P (underToLaurent R) p q w (1, s) := by
  rcases cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [placed_lower]
    exact CoefficientBassRaw1PolynomialPostcompInputFirstCell.plus_first_cell P p q w t
  · rw [placed_upper]
    rcases cover t with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · exact CoefficientBassRaw1PolynomialPostcompInputSecondCell.plus_second_cell P p q w v
    · rcases cover v with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · exact plus_third_cell P p q w z
      · exact plus_fourth_cell P p q w z

/-- The whole final minus edge is an equality in the unchanged actual polynomial triple sheet. -/
theorem minus_endpoint (s : I) :
    CoefficientBassRaw1PolynomialPostcomp.minus P p q w
      (CoefficientBassRaw1PolynomialPairCone.corrected P (underToLaurentInvert R) p q (1, s)) =
    CoefficientBassRaw1PolynomialInputCap.placedFamily P (underToLaurentInvert R) p q w (1, s) := by
  rcases cover s with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [placed_lower]
    exact CoefficientBassRaw1PolynomialPostcompInputFirstCell.minus_first_cell P p q w t
  · rw [placed_upper]
    rcases cover t with ⟨v, rfl⟩ | ⟨v, rfl⟩
    · exact CoefficientBassRaw1PolynomialPostcompInputSecondCell.minus_second_cell P p q w v
    · rcases cover v with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · exact minus_third_cell P p q w z
      · exact minus_fourth_cell P p q w z

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialPostcompInputEndpoint
