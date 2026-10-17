/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialInputAnchor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeSquareModelNormalization

/-! The full initial product row of the actual input cap in the fixed Laurent triple. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1ChartCompositionProduct
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (f : a ⟶ b) (p : b ⟶ c) (q : c ⟶ d)

/-- The initial square node followed by all three original Laurent nodes. -/
def initialNodes (j : Fin 3) : Node (reference P β f p q) :=
  CommonReferenceProduct.node (reference P β f p q)
    (chartReference P β f) (CoefficientBassLaurentCompositionCarrier.reference P p q)
    (Iso.refl _) (chartNodes P β f 2) (CoefficientBassLaurentCompositionCarrier.nodes P p q j)

/-- The first product row is the original second square node with the unchanged binary clock. -/
theorem family_initial_row (r : I) :
    family P β f p q (r, 0) = parameter (reference P β f p q)
      (initialNodes P β f p q) (binaryPath (k := 2) 0 1 2 r) := by
  dsimp only [family, ContinuousMap.comp_apply, ContinuousMap.coe_mk, chartFamily,
    Path.coe_toContinuousMap]
  rw [NativeSquareFiveSimplex.parameter.source, FiniteParameter.parameter_characteristic,
    SimplexGrid.parameter_row, parameter_face]
  apply congrArg (fun N ↦ parameter (reference P β f p q) N
    (binaryPath (k := 2) 0 1 2 r))
  funext j
  exact FiniteParameter.gridNodes_index _ _ _ _ 2 j

end Quillen.PerfectComplexes.CoefficientBassRaw1ChartCompositionProduct
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleAnchor
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (f : a ⟶ b) (p : b ⟶ c) (q : c ⟶ d)
local notation "A" => CoefficientBassRaw1ChartCompositionProduct.polynomialInput P f
local notation "F" => CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q
local notation "J" => BassMWholeNerve.coefficientModel P (β.app d)
local notation "G" => CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q
local notation "ε" => CommonReferenceNerve.CutOpenPrecomp.anchor A F J G (Iso.refl _)

/-- The literal Laurent reference transport used by the original input-cap placement. -/
abbrev inputLowerIso :=
  CoefficientBassPolynomialSheetNormalization.laurentIso (A ≫ F)
    (polynomialReference P f p q) J (A ≫ G) ε
    (CoefficientBassRaw1PolynomialInputCap.polynomialIso P f p q)

private theorem pair_iso {V W T : Model.{u}} {H₀ H₁ : V ⟶ W} {G₀ G₁ : W ⟶ T}
    (e : H₀.functor ≅ H₁.functor) (g : G₀.functor ≅ G₁.functor) :
    (Functor.uncurry.obj (whiskeringLeft V W T)).mapIso (e.prod g) =
      isoWhiskerRight e G₀.functor ≪≫ isoWhiskerLeft H₁.functor g := by
  apply Iso.ext
  rfl

private theorem product_lower_node {U V W T : Model.{u}}
    (J₀ : U ⟶ V) (L : V ⟶ W) (K : W ⟶ T) (H : U ⟶ W)
    (S : V ⟶ T) (F₀ F₁ : U ⟶ T)
    (e : F₀.functor ≅ F₁.functor) (m : F₁.functor ≅ (H ≫ K).functor)
    (τ : H.functor ≅ (J₀ ≫ L).functor)
    (α : F₀.functor ≅ (J₀ ≫ S).functor) (ρ : S.functor ≅ (L ≫ K).functor)
    (h : e ≪≫ m ≪≫ isoWhiskerRight τ K.functor = α ≪≫ isoWhiskerLeft J₀.functor ρ)
    (N : Node K) :
    CommonReferenceProduct.reanchor e
      (CommonReferenceProduct.reanchor m
        (CommonReferenceProduct.node (H ≫ K) H K (Iso.refl _) ⟨J₀ ≫ L, τ⟩ N)) =
    CommonReferenceProduct.reanchor α
      (precompNode J₀ (CommonReferenceProduct.reanchor ρ (precompNode L N))) := by
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  simp only [CommonReferenceProduct.reanchor, CommonReferenceProduct.node, precompNode,
    pair_iso, Iso.refl_trans, isoWhiskerLeft_trans]
  have hw : isoWhiskerLeft (J₀ ≫ L).functor N.2 =
      isoWhiskerLeft J₀.functor (isoWhiskerLeft L.functor N.2) := by
    apply Iso.ext
    rfl
  simpa only [Iso.trans_assoc, hw] using
    congrArg (fun z ↦ z ≪≫ isoWhiskerLeft (J₀ ≫ L).functor N.2) h

/-- Every full product node has the fixed right-first Laurent anchor after actual placement. -/
theorem input_lower_node
    (N : Node (CoefficientBassLaurentCompositionCarrier.reference P p q)) :
    CommonReferenceProduct.reanchor (inputLowerIso P β f p q)
      (CommonReferenceProduct.reanchor
        (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β f p q).symm
        (CommonReferenceProduct.node
          (CoefficientBassRaw1ChartCompositionProduct.reference P β f p q)
          (CoefficientBassRaw1ChartCompositionProduct.chartReference P β f)
          (CoefficientBassLaurentCompositionCarrier.reference P p q) (Iso.refl _)
          (CoefficientBassRaw1ChartCompositionProduct.chartNodes P β f 2) N)) =
    CommonReferenceProduct.reanchor (referenceIso P β f p q).symm
      (precompNode (BassH0Merge.normalizedMap (chart P β a))
        (CommonReferenceProduct.reanchor
          (NormalizedTripleSimplex.rightFirst
            (laurentArrow P q) (laurentArrow P p) (laurentArrow P f))
          (precompNode (BassH0Merge.normalizedMap (laurentArrow P f)) N))) := by
  have h := input_anchor P β f p q
  have ht : (CoefficientBassRaw1ChartCompositionProduct.chartNodes P β f 2).2 =
      NativeSquareModelNormalization.total (laurentArrow P f) (chart P β a) :=
    (NativeSquareModelNormalization.total_original (laurentArrow P f) (chart P β a)).symm
  rw [ht] at h
  dsimp only [CoefficientBassRaw1ChartCompositionProduct.chartNodes]
  rw [NativeSquareModelNormalization.nodes_two]
  exact product_lower_node
    (BassH0Merge.normalizedMap (chart P β a))
    (BassH0Merge.normalizedMap (laurentArrow P f))
    (CoefficientBassLaurentCompositionCarrier.reference P p q)
    (CoefficientBassRaw1ChartCompositionProduct.chartReference P β f)
    (laurentReference P f p q) _ _
    (inputLowerIso P β f p q)
    (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β f p q).symm
    (NativeSquareModelNormalization.total (laurentArrow P f) (chart P β a))
    (referenceIso P β f p q).symm
    (NormalizedTripleSimplex.rightFirst
      (laurentArrow P q) (laurentArrow P p) (laurentArrow P f)) h N

/-- The equality holds on every point of the whole original Laurent pair nerve. -/
theorem input_lower_parameter
    (y : |parameterSSet (CoefficientBassLaurentCompositionCarrier.reference P p q)|) :
    mapParameter (fun N ↦
      CommonReferenceProduct.reanchor (inputLowerIso P β f p q)
        (CommonReferenceProduct.reanchor
          (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β f p q).symm
          (CommonReferenceProduct.node
            (CoefficientBassRaw1ChartCompositionProduct.reference P β f p q)
            (CoefficientBassRaw1ChartCompositionProduct.chartReference P β f)
            (CoefficientBassLaurentCompositionCarrier.reference P p q) (Iso.refl _)
            (CoefficientBassRaw1ChartCompositionProduct.chartNodes P β f 2) N))) y =
    mapParameter (fun N ↦
      CommonReferenceProduct.reanchor (referenceIso P β f p q).symm
        (precompNode (BassH0Merge.normalizedMap (chart P β a))
          (CommonReferenceProduct.reanchor
            (NormalizedTripleSimplex.rightFirst
              (laurentArrow P q) (laurentArrow P p) (laurentArrow P f))
            (precompNode (BassH0Merge.normalizedMap (laurentArrow P f)) N)))) y := by
  exact congrArg (fun g ↦ mapParameter g y) (funext (input_lower_node P β f p q))

/-- The actual initial product family has the fixed right-first parameter before evaluation. -/
theorem input_lower_family (r : I) :
    mapParameter (CommonReferenceProduct.reanchor (inputLowerIso P β f p q))
      (mapParameter (CommonReferenceProduct.reanchor
        (CoefficientBassRaw1ChartCompositionProduct.midpointIso P β f p q).symm)
        (CoefficientBassRaw1ChartCompositionProduct.family P β f p q (r, 0))) =
    mapParameter (fun N ↦
      CommonReferenceProduct.reanchor (referenceIso P β f p q).symm
        (precompNode (BassH0Merge.normalizedMap (chart P β a))
          (CommonReferenceProduct.reanchor
            (NormalizedTripleSimplex.rightFirst
              (laurentArrow P q) (laurentArrow P p) (laurentArrow P f))
            (precompNode (BassH0Merge.normalizedMap (laurentArrow P f)) N))))
      (CoefficientBassLaurentCompositionCarrier.family P p q r) := by
  rw [CoefficientBassRaw1ChartCompositionProduct.family_initial_row]
  dsimp only [CoefficientBassLaurentCompositionCarrier.family, ContinuousMap.comp_apply]
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]
  apply congrArg (fun N ↦ parameter _ N (binaryPath (k := 2) 0 1 2 r))
  funext j
  exact input_lower_node P β f p q _

/-- Actual sheet placement carries each Laurent point by its prescribed full reference map. -/
theorem input_place_laurent (y : |parameterSSet (A ≫ G)|) :
    CoefficientBassRaw1PolynomialInputCap.place P β f p q
      (CoefficientBassRaw1PolynomialInputCap.laurent P β f p q y) =
    (SSet.toTop.map (left₀ (polynomialReference P f p q) J
      (polynomialReference P f p q ≫ J) (Iso.refl _))).hom
      (mapParameter (CommonReferenceProduct.reanchor (inputLowerIso P β f p q)) y) := by
  exact ConcreteCategory.congr_hom
    (CommonReferenceNerve.CutOpenMap.firstMap_left (A ≫ F) J (A ≫ G)
      (polynomialReference P f p q) J (polynomialReference P f p q ≫ J) ε (Iso.refl _)
      (TopCat.ofHom (mapParameter (CommonReferenceProduct.reanchor
        (CoefficientBassRaw1PolynomialInputCap.polynomialIso P f p q))))
      (TopCat.ofHom (mapParameter (CommonReferenceProduct.reanchor
        (inputLowerIso P β f p q))))
      (CoefficientBassPolynomialSheetNormalization.attachment_square (A ≫ F)
        (polynomialReference P f p q) J (A ≫ G) ε
        (CoefficientBassRaw1PolynomialInputCap.polynomialIso P f p q))) y

/-- The original placed cap has the fixed Laurent triple as its entire height-zero face. -/
theorem input_placed_lower_family (r : I) :
    CoefficientBassRaw1PolynomialInputCap.placedFamily P β f p q (r, 0) =
    (SSet.toTop.map (left₀ (polynomialReference P f p q) J
      (polynomialReference P f p q ≫ J) (Iso.refl _))).hom
      (mapParameter (fun N ↦
        CommonReferenceProduct.reanchor (referenceIso P β f p q).symm
          (precompNode (BassH0Merge.normalizedMap (chart P β a))
            (CommonReferenceProduct.reanchor
              (NormalizedTripleSimplex.rightFirst
                (laurentArrow P q) (laurentArrow P p) (laurentArrow P f))
              (precompNode (BassH0Merge.normalizedMap (laurentArrow P f)) N))))
        (CoefficientBassLaurentCompositionCarrier.family P p q r)) := by
  have hz := ((CoefficientBassRaw1PolynomialInputCap.firstSwap P β f p q).trans
    (CoefficientBassRaw1PolynomialInputCap.lastSwap P β f p q)).apply_zero r
  change CoefficientBassRaw1PolynomialInputCap.family P β f p q (r, 0) =
    CoefficientBassRaw1PolynomialInputCap.first P β f p q (r, 0) at hz
  dsimp only [CoefficientBassRaw1PolynomialInputCap.placedFamily, ContinuousMap.comp_apply]
  rw [hz]
  dsimp only [CoefficientBassRaw1PolynomialInputCap.first, ContinuousMap.comp_apply]
  rw [input_place_laurent, input_lower_family]

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialTripleAnchor
