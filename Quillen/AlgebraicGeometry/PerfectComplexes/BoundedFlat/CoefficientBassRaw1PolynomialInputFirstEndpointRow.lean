/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1ChartCompositionEndpoints
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialRadialLowerFaces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairEndpointReferences
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.PostReferenceFamily

/-! The original input cap's complete first endpoint row in the fixed polynomial triple sheet. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialInputFirstEndpointRow
open CommonReferenceNerve BassH0Merge BassH1Join
open CoefficientBassRaw1PolynomialTripleAnchor

private theorem product_source_node {V W T : Model.{u}} (H : V ⟶ W) (K : W ⟶ T)
    (N : Node H) :
    CommonReferenceProduct.node (H ≫ K) H K (Iso.refl _) N ⟨K, Iso.refl _⟩ =
      postcompNode K N := by
  have hp : (Functor.uncurry.obj (whiskeringLeft V W T)).mapIso
      (N.2.prod (Iso.refl K.functor)) =
        isoWhiskerRight N.2 K.functor ≪≫ isoWhiskerLeft N.1.functor (Iso.refl K.functor) := by
    apply Iso.ext
    rfl
  simp only [CommonReferenceProduct.node, postcompNode, hp, isoWhiskerLeft_refl,
    Iso.refl_trans, Iso.trans_refl]

private theorem post_families_match_congr {V W T : Model.{u}}
    (F : V ⟶ T) (J J' : W ⟶ T) (H : V ⟶ W) (hJ : J = J')
    (D : Fin 5 → Node H) {N M : Fin 5 → Node F}
    {ρ : F.functor ≅ (H ≫ J).functor} {ηM : F.functor ≅ (H ≫ J').functor}
    (hN : ∀ i, N i = postReferenceNode F J ρ (D i))
    (hM : ∀ i, M i = postReferenceNode F J' ηM (D i))
    (j : Fin 5) (he : N j = M j) (i : Fin 5) : N i = M i := by
  subst J'
  exact post_families_match F J H D hN hM j he i

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (f : a ⟶ b) (p : b ⟶ c) (q : c ⟶ d)

/-- The actual total Laurent coefficient map is exactly the original pair source map. -/
theorem laurent_pair_source : CoefficientBassLaurentCompositionCarrier.reference P p q =
    normalizedMap (laurentArrow P (p ≫ q)) := by
  change normalizedMap (laurentArrow P q ≫ laurentArrow P p) =
    normalizedMap (laurentArrow P (p ≫ q))
  simp only [laurentArrow, Functor.map_comp, coefficientMap_comp]

/-- The actual input placement retains each complete node of its first chart column. -/
def inputNodes (i : Fin 5) :
    Node (polynomialReference P f p q ≫ normalizedMap (chart P β d)) :=
  CommonReferenceProduct.reanchor (inputLowerIso P β f p q)
    (CommonReferenceProduct.reanchor
      (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β f p q).symm
      (CoefficientBassRaw1ChartCompositionProduct.columnNodes P β f p q 0 i))

/-- The right radial placement retains every node of the original first composite chart row. -/
def radialNodes (i : Fin 5) :
    Node (polynomialReference P f p q ≫ normalizedMap (chart P β d)) :=
  CommonReferenceProduct.reanchor
    (F₁ := CoefficientBassRaw1PolynomialPausedChart.sheetReference P β f (p ≫ q))
    (isoWhiskerRight (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P f p q)
      (normalizedMap (chart P β d)).functor)
    (CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes P β f (p ≫ q) i)

/-- Their shared source is the same original split-triple node, with its full reference. -/
theorem source_node : inputNodes P β f p q 2 = radialNodes P β f p q 2 := by
  have hi := CoefficientBassRaw1PolynomialTripleLowerFaces.input_node_row P β f p q 0
  have hr := CoefficientBassRaw1PolynomialRadialCaps.right_lower_nodes P β f p q 2
  have hf := (CoefficientBassRaw1PolynomialPairEndpointReferences.first_nodes
    P β f (p ≫ q) 2).symm.trans
      (CoefficientBassRaw1PolynomialLowerAttachment.sheet_target_nodes P β f (p ≫ q) 2)
  exact (hi.trans hr.symm).trans (congrArg (CommonReferenceProduct.reanchor
    (F₀ := polynomialReference P f p q ≫ normalizedMap (chart P β d))
    (F₁ := CoefficientBassRaw1PolynomialPausedChart.sheetReference P β f (p ≫ q))
    (isoWhiskerRight (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P f p q)
      (normalizedMap (chart P β d)).functor)) hf.symm)

/-- All five complete nodes agree before any native evaluation or change of square clock. -/
theorem nodes (i : Fin 5) : inputNodes P β f p q i = radialNodes P β f p q i := by
  apply post_families_match_congr
    (polynomialReference P f p q ≫ normalizedMap (chart P β d))
    (CoefficientBassLaurentCompositionCarrier.reference P p q)
    (normalizedMap (laurentArrow P (p ≫ q)))
    (CoefficientBassRaw1ChartCompositionProduct.chartReference P β f)
    (laurent_pair_source P p q) (CoefficientBassRaw1ChartCompositionProduct.chartNodes P β f)
    (ρ := inputLowerIso P β f p q ≪≫
      (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β f p q).symm)
    (ηM := isoWhiskerRight
      (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P f p q)
        (normalizedMap (chart P β d)).functor ≪≫
      CoefficientBassRaw1PolynomialPausedChart.sheetAnchor P β f (p ≫ q) ≪≫
      CoefficientMovingSquareRows.firstAnchor
        (polynomialArrow P f) (polynomialArrow P (p ≫ q))
        (laurentArrow P f) (laurentArrow P (p ≫ q))
        (chart P β a) (chart P β b) (chart P β d)
        (coefficientMap_naturality P β f).symm
        (coefficientMap_naturality P β (p ≫ q)).symm)
    ?_ ?_ 2 (source_node P β f p q) i
  · intro j
    dsimp only [inputNodes, CoefficientBassRaw1ChartCompositionProduct.columnNodes]
    rw [show CoefficientBassLaurentCompositionCarrier.nodes P p q 0 =
      ⟨CoefficientBassLaurentCompositionCarrier.reference P p q, Iso.refl _⟩ from rfl,
      product_source_node]
    simp only [CommonReferenceProduct.reanchor, postcompNode, postReferenceNode,
      Iso.trans_assoc]
  · intro j
    simp only [radialNodes, CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes,
      CommonReferenceProduct.reanchor, postReferenceNode, Iso.trans_assoc]

/-- The full original five-node square parameter is unchanged by actual endpoint placement. -/
theorem family (t : I) :
    mapParameter (CommonReferenceProduct.reanchor (inputLowerIso P β f p q))
      (mapParameter (CommonReferenceProduct.reanchor
        (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β f p q).symm)
        (CoefficientBassRaw1ChartCompositionProduct.family P β f p q (0, t))) =
      mapParameter (CommonReferenceProduct.reanchor
        (F₀ := polynomialReference P f p q ≫ normalizedMap (chart P β d))
        (F₁ := CoefficientBassRaw1PolynomialPausedChart.sheetReference P β f (p ≫ q))
        (isoWhiskerRight (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P f p q)
          (normalizedMap (chart P β d)).functor))
        (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β f (p ≫ q))
          (CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes P β f (p ≫ q))
          (NativeSquareFiveSimplex.parameter t)) := by
  rw [CoefficientBassRaw1ChartCompositionProduct.family_zero,
    mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun N ↦ parameter
    (polynomialReference P f p q ≫ normalizedMap (chart P β d)) N
    (NativeSquareFiveSimplex.parameter t)) (funext (nodes P β f p q))

/-- The actual placed first half is the complete first row of the right radial cap. -/
theorem placed_first (t : I) :
    CoefficientBassRaw1PolynomialInputCap.place P β f p q
      (CoefficientBassRaw1PolynomialInputCap.first P β f p q (0, t)) =
    CoefficientBassRaw1PolynomialRadialCaps.rightMap P β f p q
      (CoefficientBassRaw1PolynomialPairCone.laurent P β f (p ≫ q)
        (parameter (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β f (p ≫ q))
          (CoefficientBassRaw1PolynomialPairEndpointReferences.firstNodes P β f (p ≫ q))
          (NativeSquareFiveSimplex.parameter t))) := by
  dsimp only [CoefficientBassRaw1PolynomialInputCap.first, ContinuousMap.comp_apply]
  rw [input_place_laurent, family]
  symm
  change CoefficientBassPolynomialSheetNormalization.map
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P f (p ≫ q))
    (polynomialReference P f p q) (normalizedMap (chart P β d))
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β f (p ≫ q))
    (Iso.refl _) (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P f p q)
    (SSet.toTop.map (CommonReferenceNerve.CutOpenCarrier.left₀ _ _ _ _) _) = _
  rw [CoefficientBassPolynomialSheetNormalization.map_laurent]
  have hn : CoefficientBassPolynomialSheetNormalization.laurentIso
      (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P f (p ≫ q))
      (polynomialReference P f p q) (normalizedMap (chart P β d))
      (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β f (p ≫ q))
      (Iso.refl _) (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P f p q) =
      isoWhiskerRight (CoefficientBassRaw1PolynomialRadialCaps.rightPolynomialIso P f p q)
        (normalizedMap (chart P β d)).functor := Iso.trans_refl _
  rw [hn]
  rfl

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialInputFirstEndpointRow
