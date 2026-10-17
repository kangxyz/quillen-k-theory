/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialInputFirstEndpointRow
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialInputPolynomialEndpoint
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialDirectSquareReference
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PreReferenceFamily
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairEndpointCells

/-! The original input cap's complete second endpoint row, with its full terminal attachment. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialInputSecondEndpointRow
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier BassH0Merge BassH1Join
open CoefficientBassRaw1PolynomialTripleAnchor

private theorem attach_refl {V W T : Model.{u}} (F : V ⟶ W) (J : W ⟶ T) (N : Node F) :
    attachPostcompNode F J (F ≫ J) (Iso.refl _) N = postcompNode J N := by
  simp only [attachPostcompNode, postcompNode, Iso.refl_trans]

private theorem reanchor_post {V W T : Model.{u}} {F F' : V ⟶ W}
    (J : W ⟶ T) (δ : F'.functor ≅ F.functor) (N : Node F) :
    CommonReferenceProduct.reanchor (isoWhiskerRight δ (J).functor) (postcompNode J N) =
      postcompNode J (CommonReferenceProduct.reanchor δ N) := by
  simp only [CommonReferenceProduct.reanchor, postcompNode, isoWhiskerRight_trans]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (f : a ⟶ b) (p : b ⟶ c) (q : c ⟶ d)
local notation "A" => CoefficientBassRaw1ChartCompositionProduct.polynomialInput P f
local notation "F" => CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q
local notation "J" => BassMWholeNerve.coefficientModel P (β.app d)
local notation "G" => CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q
local notation "ε" => CutOpenPrecomp.anchor A F J G (Iso.refl _)

/-- The actual placement commutes with each complete source-precomposed attachment node. -/
theorem input_attachment_node (N : Node F) :
    CommonReferenceProduct.reanchor (inputLowerIso P β f p q)
      (precompNode A (postcompNode J N)) =
    postcompNode J (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1PolynomialInputCap.polynomialIso P f p q) (precompNode A N)) := by
  have hp := CutOpenPrecomp.attachment_node A F J G (Iso.refl _) N
  rw [attach_refl] at hp
  have hn := CoefficientBassPolynomialSheetNormalization.attachment_node (A ≫ F)
    (polynomialReference P f p q) J (A ≫ G) ε
    (CoefficientBassRaw1PolynomialInputCap.polynomialIso P f p q) (precompNode A N)
  rw [attach_refl] at hn
  exact (congrArg (CommonReferenceProduct.reanchor (inputLowerIso P β f p q)) hp).trans hn

/-- The complete second input row keeps the original outer pair square. -/
def inputNodes (i : Fin 5) : Node (polynomialReference P f p q ≫ J) :=
  CommonReferenceProduct.reanchor (inputLowerIso P β f p q)
    (precompNode A (CoefficientBassRaw1PolynomialPairEndpointReferences.outerNodes P β p q i))

/-- The complete radial row keeps its original precomposed composite-arrow square. -/
def radialNodes (i : Fin 5) : Node (polynomialReference P f p q ≫ J) :=
  CommonReferenceProduct.reanchor
    (F₁ := CoefficientBassRaw1PolynomialPausedChart.sheetReference P β f (p ≫ q))
    (isoWhiskerRight (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P f p q)
      (J).functor)
    (CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes P β f (p ≫ q) i)

/-- The original polynomial endpoint fixes their full shared terminal reference node. -/
theorem terminal_node : inputNodes P β f p q 4 = radialNodes P β f p q 4 := by
  have ho := (CoefficientBassRaw1PolynomialPairEndpointReferences.outer_nodes P β p q 4).symm.trans
    (CoefficientBassRaw1PolynomialSourceAttachment.sheet_source_nodes P β p q 0)
  have hs := (CoefficientBassRaw1PolynomialPairEndpointReferences.second_nodes
    P β f (p ≫ q) 4).symm.trans
      (CoefficientBassRaw1PolynomialSourceAttachment.sheet_source_nodes P β f (p ≫ q) 2)
  dsimp only [inputNodes, radialNodes]
  rw [ho, hs, input_attachment_node, reanchor_post]
  exact congrArg (postcompNode J)
    (CoefficientBassRaw1PolynomialInputPolynomialEndpoint.polynomial_node P f p q)

/-- Every complete second row node agrees, with its original polynomial precomposition. -/
theorem nodes (i : Fin 5) : inputNodes P β f p q i = radialNodes P β f p q i := by
  apply pre_families_match (polynomialReference P f p q ≫ J) A
    (CoefficientBassRaw1PolynomialDirectSquareReference.directSource P β p q)
    (CoefficientBassRaw1PolynomialDirectSquareReference.directNodes P β p q)
    (ρ := inputLowerIso P β f p q ≪≫ isoWhiskerLeft (A).functor
      (CoefficientBassRaw1PolynomialDirectSquareReference.directAnchor P β p q))
    («σ» := isoWhiskerRight
      (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P f p q) (J).functor ≪≫
      CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β f (p ≫ q) ≪≫
      CoefficientMovingSquareRows.secondAnchor
        (polynomialArrow P f) (polynomialArrow P (p ≫ q)) (laurentArrow P (p ≫ q))
        (chart P β b) (chart P β d) (coefficientMap_naturality P β (p ≫ q)).symm)
    ?_ ?_ 4 (terminal_node P β f p q) i
  · intro j
    dsimp only [inputNodes]
    rw [← CoefficientBassRaw1PolynomialDirectSquareReference.normalized_direct_nodes]
    simp only [CommonReferenceProduct.reanchor, precompNode, preReferenceNode,
      isoWhiskerLeft_trans, Iso.trans_assoc]
  · intro j
    simp only [radialNodes, CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes,
      CommonReferenceProduct.reanchor, preReferenceNode, Iso.trans_assoc]
    rfl

/-- The original second square clock is unchanged before inclusion or native evaluation. -/
theorem family (t : I) :
    mapParameter (CommonReferenceProduct.reanchor (inputLowerIso P β f p q))
      (mapParameter (precompNode A)
        (parameter G (CoefficientBassRaw1PolynomialPairEndpointReferences.outerNodes P β p q)
          (NativeSquareFiveSimplex.parameter t))) =
    mapParameter (CommonReferenceProduct.reanchor
      (F₀ := polynomialReference P f p q ≫ J)
      (F₁ := CoefficientBassRaw1PolynomialPausedChart.sheetReference P β f (p ≫ q))
      (isoWhiskerRight (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P f p q)
        (J).functor))
      (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β f (p ≫ q))
        (CoefficientBassRaw1PolynomialPairEndpointReferences.secondNodes P β f (p ≫ q))
        (NativeSquareFiveSimplex.parameter t)) := by
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun N ↦ parameter (polynomialReference P f p q ≫ J) N
    (NativeSquareFiveSimplex.parameter t)) (funext (nodes P β f p q))

/-- The original source-precomposition map carries the entire Laurent summand literally. -/
theorem precomp_laurent (y : |parameterSSet G|) :
    CoefficientBassRaw1PolynomialInputCap.precomp P β f p q
      (CoefficientBassRaw1PolynomialPairCone.laurent P β p q y) =
    CoefficientBassRaw1PolynomialInputCap.laurent P β f p q
      (mapParameter (precompNode A) y) :=
  ConcreteCategory.congr_hom (CutOpenPrecomp.firstMap_left A F J G (Iso.refl _)) y

/-- The actual placed second half is the original right radial second path at the same clock. -/
theorem placed_second (t : I) :
    CoefficientBassRaw1PolynomialInputCap.place P β f p q
      (CoefficientBassRaw1PolynomialInputCap.precomp P β f p q
        (CoefficientBassRaw1PolynomialPairCone.chartSquare P β p q (0, t))) =
    CoefficientBassRaw1PolynomialRadialCaps.rightMap P β f p q
      (CoefficientBassRaw1PolynomialPairCone.secondPath P β f (p ≫ q) t) := by
  have ho := funext (CoefficientBassRaw1PolynomialPairEndpointReferences.outer_nodes P β p q)
  have hs := funext
    (CoefficientBassRaw1PolynomialPairEndpointReferences.second_nodes P β f (p ≫ q))
  rw [CoefficientBassRaw1PolynomialPairCone.chartSquare_zero,
    CoefficientBassRaw1PolynomialPairCone.secondPath_row, ho, hs,
    precomp_laurent, input_place_laurent, family]
  symm
  change CoefficientBassPolynomialSheetNormalization.map
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P f (p ≫ q))
    (polynomialReference P f p q) J
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β f (p ≫ q))
    (Iso.refl _) (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P f p q)
    (SSet.toTop.map (CommonReferenceNerve.CutOpenCarrier.left₀ _ _ _ _) _) = _
  rw [CoefficientBassPolynomialSheetNormalization.map_laurent]
  have hn : CoefficientBassPolynomialSheetNormalization.laurentIso
      (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P f (p ≫ q))
      (polynomialReference P f p q) J
      (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β f (p ≫ q))
      (Iso.refl _) (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P f p q) =
      isoWhiskerRight (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P f p q)
        (J).functor := Iso.trans_refl _
  rw [hn]

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialInputSecondEndpointRow
