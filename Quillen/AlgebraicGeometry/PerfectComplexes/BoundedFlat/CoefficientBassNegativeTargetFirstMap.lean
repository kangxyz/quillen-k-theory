/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeTargetChartAttachment
public import Quillen.Topology.DoubleMappingCylinder.HomotopyDescent

/-! The actual chart-square path followed by the target cylinder, with two separate tips. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassNegativeTargetFirstMap
open CommonReferenceNerve CutOpenCarrier CoefficientBassNegativeTargetChartAttachment
private theorem realized_left {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    (y : |Y|) :
    SSet.toTop.map ((coprod.inl : Y ⟶ Y ⨿ Z) ≫
      DoubleCylinder.simplicialEnds f g) y =
        DoubleCylinder.realizedEnds f g (Sum.inl y) := by
  have h : SSet.toTop.map ((coprod.inl : Y ⟶ Y ⨿ Z) ≫
      DoubleCylinder.simplicialEnds f g) =
      (TopCat.binaryCofan |Y| |Z|).inl ≫ DoubleCylinder.realizedEnds f g := by
    simpa only [Functor.map_comp, DoubleCylinder.realizedEnds, Category.assoc,
      Iso.hom_inv_id_assoc] using
      congrArg (fun k ↦ k ≫ (realizationBinarySumIso Y Z).inv ≫
        SSet.toTop.map (DoubleCylinder.simplicialEnds f g))
        (realizationBinarySumIso_inl Y Z)
  exact ConcreteCategory.congr_hom h y

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (D : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (polynomialUnderFunctor R).obj a))))
  (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (laurentUnderFunctor R).obj a))))
  (ε₀ ε₁ : G.functor ≅ (D ≫ Ja P (a := a)).functor)

/-- The target cut-open carrier with both original anchors transported along `f`. -/
abbrev targetSpace := CutOpenCarrier.space (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
  (targetAnchor P f D G ε₀) (targetAnchor P f D G ε₁)
/-- The source cut-open carrier retaining the two supplied anchors `ε₀` and `ε₁`. -/
abbrev sourceSpace := CutOpenCarrier.space D (Ja P (a := a)) G ε₀ ε₁
/-- The whole Laurent-reference inclusion into the target cut-open carrier. -/
abbrev targetLaurent := laurentInclusion (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
  (targetAnchor P f D G ε₀) (targetAnchor P f D G ε₁)
/-- Postcompose every full polynomial reference node by the original polynomial map of `f`. -/
def polynomialMap := mapParameter (postcompNode (M P f) (F := D))
/-- Postcompose the full Laurent reference by its original map of `f`, then include it in the
target. -/
def laurentMap : C(|parameterSSet G|, targetSpace P f D G ε₀ ε₁) :=
  (targetLaurent P f D G ε₀ ε₁).comp (mapParameter (postcompNode (L P f)))

/-- Select `ε₁` for the plus sheet and `ε₀` for the minus sheet. -/
abbrev sheetAnchor (e : Bool) := if e then ε₁ else ε₀

/-- Select the target carrier's distinct plus or minus tip using the original sheet label. -/
def tip (e : Bool) : targetSpace P f D G ε₀ ε₁ :=
  if e then tipPlus (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
    (targetAnchor P f D G ε₀) (targetAnchor P f D G ε₁)
  else tipMinus (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
    (targetAnchor P f D G ε₀) (targetAnchor P f D G ε₁)

/-- The target polynomial cylinder for the selected sheet, retaining its original anchor and
height. -/
def cylinder (e : Bool) : C(|parameterSSet (D ≫ M P f)| × I,
    targetSpace P f D G ε₀ ε₁) :=
  if e then cylinderPlus (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
    (targetAnchor P f D G ε₀) (targetAnchor P f D G ε₁)
  else cylinderMinus (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
    (targetAnchor P f D G ε₀) (targetAnchor P f D G ε₁)

private theorem parameter_comp {V₀ W₀ V₁ W₁ V₂ W₂ : Model.{v}}
    {F₀ : V₀ ⟶ W₀} {F₁ : V₁ ⟶ W₁} {F₂ : V₂ ⟶ W₂}
    (g : Node F₀ → Node F₁) (h : Node F₁ → Node F₂) (y : |parameterSSet F₀|) :
    mapParameter h (mapParameter g y) = mapParameter (fun N ↦ h (g N)) y := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter F₀ y
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]

/-- Attach the selected source polynomial sheet before the original Laurent postcomposition. -/
abbrev startMap (e : Bool) := (laurentMap P f D G ε₀ ε₁).comp
  (mapParameter (attachPostcompNode D (Ja P (a := a)) G (sheetAnchor P D G ε₀ ε₁ e)))
/-- Postcompose the polynomial reference and attach it through the transported selected anchor. -/
abbrev middleMap (e : Bool) := (targetLaurent P f D G ε₀ ε₁).comp
  ((mapParameter (attachPostcompNode (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
    (targetAnchor P f D G (sheetAnchor P D G ε₀ ε₁ e)))).comp (polynomialMap P f D))

/-- The full original chart square runs before the target polynomial contraction. -/
def chartTrack (e : Bool) : (startMap P f D G ε₀ ε₁ e).Homotopy
    (middleMap P f D G ε₀ ε₁ e) where
  toFun z := targetLaurent P f D G ε₀ ε₁
    (moving P f D G (sheetAnchor P D G ε₀ ε₁ e) (z.2, z.1))
  continuous_toFun := by fun_prop
  map_zero_left y := by
    rw [moving_zero_attachment]
    exact congrArg (targetLaurent P f D G ε₀ ε₁) (parameter_comp _ _ y).symm
  map_one_left y := by
    rw [moving_one_attachment]
    exact congrArg (targetLaurent P f D G ε₀ ε₁) (parameter_comp _ _ y).symm

/-- The second half uses the literal target sheet and its own tip. -/
def contraction (e : Bool) : (middleMap P f D G ε₀ ε₁ e).Homotopy
    (ContinuousMap.const _ (tip P f D G ε₀ ε₁ e)) where
  toFun z := cylinder P f D G ε₀ ε₁ e (polynomialMap P f D z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left y := by
    cases e with
    | false => exact cylinderMinus_zero _ _ _ _ _ _
    | true => exact cylinderPlus_zero _ _ _ _ _ _
  map_one_left y := by
    cases e with
    | false => exact cylinderMinus_one _ _ _ _ _ _
    | true => exact cylinderPlus_one _ _ _ _ _ _

/-- Both half clocks are the original cone-map null word, rather than a direct target cylinder. -/
def nullTrack (e : Bool) :=
  (chartTrack P f D G ε₀ ε₁ e).trans (contraction P f D G ε₀ ε₁ e)

/-- The first genuine displayed pushout descends the prescribed ordinary null track. -/
def firstMap : C(|firstSimplicial D (Ja P (a := a)) G ε₀|,
    targetSpace P f D G ε₀ ε₁) :=
  DoubleCylinder.homotopyDesc
    (SSet.toTop.map (attaching D (Ja P (a := a)) G ε₀)) (SSet.toTop.map (erase D))
    (first_isPushout D (Ja P (a := a)) G ε₀) (laurentMap P f D G ε₀ ε₁)
    (ContinuousMap.const _ (tip P f D G ε₀ ε₁ false)) (nullTrack P f D G ε₀ ε₁ false)


/-- The first descent retains the full Laurent map, including its reference anchors. -/
theorem firstMap_laurent (y : |parameterSSet G|) :
    firstMap P f D G ε₀ ε₁ (SSet.toTop.map (left₀ D (Ja P (a := a)) G ε₀) y) =
      laurentMap P f D G ε₀ ε₁ y := by
  have h := ContinuousMap.congr_fun (DoubleCylinder.homotopyDesc_left
    (SSet.toTop.map (attaching D (Ja P (a := a)) G ε₀))
    (SSet.toTop.map (erase D)) (first_isPushout D (Ja P (a := a)) G ε₀)
    (laurentMap P f D G ε₀ ε₁)
    (ContinuousMap.const _ (tip P f D G ε₀ ε₁ false))
    (nullTrack P f D G ε₀ ε₁ false)) y
  exact (congrArg (firstMap P f D G ε₀ ε₁)
    (realized_left (attaching D (Ja P (a := a)) G ε₀) (erase D) y)).trans h

/-- The first-sheet cylinder retains both literal original half clocks. -/
theorem firstMap_cylinder (y : |parameterSSet D|) (t : I) :
    firstMap P f D G ε₀ ε₁
      (DoubleCylinder.realizedCylinder
        (attaching D (Ja P (a := a)) G ε₀) (erase D) (y, ULift.up t)) =
      nullTrack P f D G ε₀ ε₁ false (t, y) :=
  DoubleCylinder.homotopyDesc_apply_cylinder
    (SSet.toTop.map (attaching D (Ja P (a := a)) G ε₀))
    (SSet.toTop.map (erase D)) (first_isPushout D (Ja P (a := a)) G ε₀)
    (laurentMap P f D G ε₀ ε₁)
    (ContinuousMap.const _ (tip P f D G ε₀ ε₁ false))
    (nullTrack P f D G ε₀ ε₁ false) t y

end Quillen.PerfectComplexes.CoefficientBassNegativeTargetFirstMap
