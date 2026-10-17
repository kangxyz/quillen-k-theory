/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConePairChartFaces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialSourceProjection

/-! The original pair sheet retains its source projection and exact ordinary attachment. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.PairProjection
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open BassProjectionPath.WholeReference

private theorem precomp_laurent_iso {U V W T : Model.{u}}
    (A : U ⟶ V) (F : V ⟶ W) (F' : U ⟶ W) (J : W ⟶ T)
    (e : F'.functor ≅ (A ≫ F).functor) :
    CoefficientBassPolynomialSheetNormalization.laurentIso (A ≫ F) F' J
      (A ≫ (F ≫ J))
      (CutOpenPrecomp.anchor A F J (F ≫ J) (Iso.refl _)) e =
      isoWhiskerRight e J.functor := by
  apply Iso.ext
  apply NatTrans.ext
  funext x
  change J.functor.map (e.hom.app x) ≫ (𝟙 _ ≫ 𝟙 _) = J.functor.map (e.hom.app x)
  simp only [Category.comp_id]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
local notation "E" => inputReference P p q
local notation "F" => CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q
local notation "A" => normalizedMap (polynomialProjection P a)
local notation "Jc" => normalizedMap (polynomialProjection P c)
local notation "H" => BassProjectionPath.WholeReference.reference P c E
variable (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hc : coefficientMap P (β.app c) ≫ polynomialProjection P c = laurentProjection P c)
local notation "J" => BassMWholeNerve.coefficientModel P (β.app c)
local notation "G" => CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p q
local notation "ε" => CutOpenPrecomp.anchor A F J G (Iso.refl _)

/-- Precompose a whole polynomial node by the original source projection, then reanchor it at
the target. -/
def polynomialNode (N : Node F) : Node (E ≫ Jc) :=
  CommonReferenceProduct.reanchor (PairLowerReference.polynomialAnchor P p q) (precompNode A N)

/-- The displayed precomposition anchor retains the literal sheet reference. -/
def laurentIso : (H).functor ≅ (A ≫ G).functor :=
  isoWhiskerLeft (E).functor (BassMJoin.projectionEndpointIso P β hc) ≪≫
    CoefficientBassPolynomialSheetNormalization.laurentIso
      (A ≫ F) (E ≫ Jc) J (A ≫ G) ε (PairLowerReference.polynomialAnchor P p q)

theorem laurentIso_chart : laurentIso P p q β hc =
    PairLowerReference.chartAnchor P p q β hc := by
  unfold laurentIso
  rw [precomp_laurent_iso]
  rfl

/-- Precompose a whole Laurent node and reanchor it through the supplied target chart equation
`hc`. -/
def laurentNode (N : Node G) : Node H :=
  CommonReferenceProduct.reanchor (laurentIso P p q β hc) (precompNode A N)

/-- The continuous whole-node Laurent projection induced by the original source projection and
`hc`. -/
def laurent : C(|parameterSSet G|, |parameterSSet H|) := mapParameter (laurentNode P p q β hc)
/-- The continuous whole-node polynomial projection into the original target-projected reference. -/
def polynomial : C(|parameterSSet F|, |parameterSSet (E ≫ Jc)|) :=
  mapParameter (polynomialNode P p q)

/-- Both full references commute before applying the cone quotient. -/
theorem attachment_node (N : Node F) :
    laurentNode P p q β hc (attachPostcompNode F J G (Iso.refl _) N) =
      chartAttachmentNode P c E β hc (polynomialNode P p q N) := by
  dsimp only [laurentNode]
  rw [CutOpenPrecomp.attachment_node]
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  simp only [laurentIso, CoefficientBassPolynomialSheetNormalization.laurentIso,
    chartAttachmentNode, CommonReferenceProduct.postNode, CommonReferenceProduct.reanchor,
    attachPostcompNode, postcompNode, polynomialNode, isoWhiskerRight_trans,
    Iso.trans_assoc, Iso.symm_self_id_assoc]
  rfl

theorem attachment_parameter (y : |parameterSSet F|) :
    laurent P p q β hc (mapParameter (attachPostcompNode F J G (Iso.refl _)) y) =
      mapParameter (chartAttachmentNode P c E β hc) (polynomial P p q y) := by
  obtain ⟨n, ns, z, rfl⟩ := exists_parameter F y
  dsimp only [laurent, polynomial]
  rw [mapParameter_parameter, mapParameter_parameter,
    mapParameter_parameter, mapParameter_parameter]
  exact congrArg (fun ts ↦ CommonReferenceNerve.parameter H ts z)
    (funext (fun i ↦ attachment_node P p q β hc (ns i)))

theorem laurent_projected
    (h : PairLowerReference.chartAnchor P p q β hc =
      PairLowerReference.projectedAnchor P p q β hc) :
    laurent P p q β hc = PairLowerReference.projectedChart P p q β hc := by
  unfold laurent laurentNode
  rw [laurentIso_chart, h]
  rfl

/-- The positive raw chart face is literally the frozen original M face. -/
theorem plus_chart_face (r s : I) :
    laurent P p q (underToLaurent R) (laurentPlus_projection P c)
      (CoefficientBassRaw1PolynomialPausedChart.sheetFamily P (underToLaurent R) p q (r, s)) =
    laurentCube P p q (r, (s, 0)) := by
  rw [laurent_projected P p q _ _ (PairLowerReference.plus_chart_anchor P p q)]
  exact PairLowerReference.plus_chart_face P p q r s

/-- The inverse raw chart face keeps its independent full reference and old pause. -/
theorem minus_chart_face (r s : I) :
    laurent P p q (underToLaurentInvert R) (laurentMinus_projection P c)
      (CoefficientBassRaw1PolynomialPausedChart.sheetFamily P
        (underToLaurentInvert R) p q (r, s)) = laurentCube P p q (r, (s, 1)) := by
  rw [laurent_projected P p q _ _ (PairLowerReference.minus_chart_anchor P p q)]
  exact PairLowerReference.minus_chart_face P p q r s

end Quillen.PerfectComplexes.BassMWholeConeCarrier.PairProjection
