/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSeedTargetChartAttachment
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
namespace Quillen.PerfectComplexes.CoefficientBassSeedTargetCylinderMap
open CommonReferenceNerve CutOpenCarrier CoefficientBassSeedTargetChartAttachment
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

private theorem realized_right {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    (z : |Z|) :
    SSet.toTop.map ((coprod.inr : Z ⟶ Y ⨿ Z) ≫
      DoubleCylinder.simplicialEnds f g) z =
        DoubleCylinder.realizedEnds f g (Sum.inr z) := by
  have h : SSet.toTop.map ((coprod.inr : Z ⟶ Y ⨿ Z) ≫
      DoubleCylinder.simplicialEnds f g) =
      (TopCat.binaryCofan |Y| |Z|).inr ≫ DoubleCylinder.realizedEnds f g := by
    simpa only [Functor.map_comp, DoubleCylinder.realizedEnds, Category.assoc,
      Iso.hom_inv_id_assoc] using
      congrArg (fun k ↦ k ≫ (realizationBinarySumIso Y Z).inv ≫
        SSet.toTop.map (DoubleCylinder.simplicialEnds f g))
        (realizationBinarySumIso_inr Y Z)
  exact ConcreteCategory.congr_hom h z


variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (D : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (polynomialUnderFunctor R).obj a))))
  (G : V ⟶ modelOf (boundedFlatPerfectWaldhausen
    (space (op P, (laurentUnderFunctor R).obj a))))
  (ε₀ ε₁ : G.functor ≅ (D ≫ Ja P (a := a)).functor)

/-- The target cut-open carrier with both coefficient-transported sheet anchors. -/
abbrev targetSpace := CutOpenCarrier.space (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
  (targetAnchor P f D G ε₀) (targetAnchor P f D G ε₁)
/-- The source cut-open carrier with the two original sheet anchors. -/
abbrev sourceSpace := CutOpenCarrier.space D (Ja P (a := a)) G ε₀ ε₁
/-- The Laurent parameter inclusion into the target cut-open carrier. -/
abbrev targetLaurent := laurentInclusion (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
  (targetAnchor P f D G ε₀) (targetAnchor P f D G ε₁)
/-- The map of polynomial parameter spaces induced by postcomposition with `M P f`. -/
def polynomialMap := mapParameter (postcompNode (M P f) (F := D))
/-- The Laurent parameter map followed by inclusion in the target cut-open carrier. -/
def laurentMap : C(|parameterSSet G|, targetSpace P f D G ε₀ ε₁) :=
  (targetLaurent P f D G ε₀ ε₁).comp (mapParameter (postcompNode (L P f)))

/-- Select the source anchor `ε₀` for `false` and `ε₁` for `true`. -/
abbrev sheetAnchor (e : Bool) := if e then ε₁ else ε₀

/-- Select the target tip corresponding to the Boolean sheet label. -/
def tip (e : Bool) : targetSpace P f D G ε₀ ε₁ :=
  if e then tipPlus (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
    (targetAnchor P f D G ε₀) (targetAnchor P f D G ε₁)
  else tipMinus (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
    (targetAnchor P f D G ε₀) (targetAnchor P f D G ε₁)

/-- Select the target cylinder corresponding to the Boolean sheet label. -/
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

/-- The route through the selected source attachment and Laurent map into the target carrier. -/
abbrev startMap (e : Bool) := (laurentMap P f D G ε₀ ε₁).comp
  (mapParameter (attachPostcompNode D (Ja P (a := a)) G (sheetAnchor P D G ε₀ ε₁ e)))
/-- The route through the polynomial map and selected target attachment into the target carrier. -/
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

/-- The shifted sheet begins at its actual attachment to the first pushout. -/
def secondNull : ((firstMap P f D G ε₀ ε₁).comp
    (SSet.toTop.map (secondAttaching D (Ja P (a := a)) G ε₀ ε₁)).hom).Homotopy
    ((ContinuousMap.const _ (tip P f D G ε₀ ε₁ true)).comp
      (SSet.toTop.map (erase D)).hom) where
  toFun := nullTrack P f D G ε₀ ε₁ true
  continuous_toFun := (nullTrack P f D G ε₀ ε₁ true).continuous_toFun
  map_zero_left y := by
    refine ((nullTrack P f D G ε₀ ε₁ true).map_zero_left y).trans ?_
    dsimp only [secondAttaching]
    rw [Functor.map_comp]
    exact (firstMap_laurent P f D G ε₀ ε₁
      (mapParameter (attachPostcompNode D (Ja P (a := a)) G ε₁) y)).symm
  map_one_left y := (nullTrack P f D G ε₀ ε₁ true).map_one_left y

/-- Both original sheets descend with the chart track followed by target contraction. -/
def map : C(sourceSpace P D G ε₀ ε₁, targetSpace P f D G ε₀ ε₁) :=
  DoubleCylinder.homotopyDesc
    (SSet.toTop.map (secondAttaching D (Ja P (a := a)) G ε₀ ε₁))
    (SSet.toTop.map (erase D)) (second_isPushout D (Ja P (a := a)) G ε₀ ε₁)
    (firstMap P f D G ε₀ ε₁) (ContinuousMap.const _ (tip P f D G ε₀ ε₁ true))
    (secondNull P f D G ε₀ ε₁)


/-- The second descent leaves the entire first sheet map unchanged. -/
theorem map_first (x : |firstSimplicial D (Ja P (a := a)) G ε₀|) :
    map P f D G ε₀ ε₁ (SSet.toTop.map (left₁ D (Ja P (a := a)) G ε₀ ε₁) x) =
      firstMap P f D G ε₀ ε₁ x := by
  have h := ContinuousMap.congr_fun (DoubleCylinder.homotopyDesc_left
    (SSet.toTop.map (secondAttaching D (Ja P (a := a)) G ε₀ ε₁))
    (SSet.toTop.map (erase D)) (second_isPushout D (Ja P (a := a)) G ε₀ ε₁)
    (firstMap P f D G ε₀ ε₁) (ContinuousMap.const _ (tip P f D G ε₀ ε₁ true))
    (secondNull P f D G ε₀ ε₁)) x
  exact (congrArg (map P f D G ε₀ ε₁)
    (realized_left (secondAttaching D (Ja P (a := a)) G ε₀ ε₁) (erase D) x)).trans h

/-- The shared Laurent family is acted on by the original full model map. -/
theorem map_laurent (y : |parameterSSet G|) :
    map P f D G ε₀ ε₁ (laurentInclusion D (Ja P (a := a)) G ε₀ ε₁ y) =
      laurentMap P f D G ε₀ ε₁ y :=
  (map_first P f D G ε₀ ε₁ _).trans (firstMap_laurent P f D G ε₀ ε₁ y)

/-- The ordinary sheet retains the complete original chart-then-contraction word. -/
theorem map_cylinderMinus (y : |parameterSSet D|) (t : I) :
    map P f D G ε₀ ε₁ (cylinderMinus D (Ja P (a := a)) G ε₀ ε₁ (y, t)) =
      nullTrack P f D G ε₀ ε₁ false (t, y) :=
  (map_first P f D G ε₀ ε₁ _).trans
    (DoubleCylinder.homotopyDesc_apply_cylinder
      (SSet.toTop.map (attaching D (Ja P (a := a)) G ε₀))
      (SSet.toTop.map (erase D)) (first_isPushout D (Ja P (a := a)) G ε₀)
      (laurentMap P f D G ε₀ ε₁)
      (ContinuousMap.const _ (tip P f D G ε₀ ε₁ false))
      (nullTrack P f D G ε₀ ε₁ false) t y)

/-- The shifted sheet keeps the same original clock with its own full unit-shifted anchor. -/
theorem map_cylinderPlus (y : |parameterSSet D|) (t : I) :
    map P f D G ε₀ ε₁ (cylinderPlus D (Ja P (a := a)) G ε₀ ε₁ (y, t)) =
      nullTrack P f D G ε₀ ε₁ true (t, y) :=
  DoubleCylinder.homotopyDesc_apply_cylinder
    (SSet.toTop.map (secondAttaching D (Ja P (a := a)) G ε₀ ε₁))
    (SSet.toTop.map (erase D)) (second_isPushout D (Ja P (a := a)) G ε₀ ε₁)
    (firstMap P f D G ε₀ ε₁) (ContinuousMap.const _ (tip P f D G ε₀ ε₁ true))
    (secondNull P f D G ε₀ ε₁) t y

/-- The two tips go to the two prescribed target tips without an extra quotient. -/
theorem map_tipMinus :
    map P f D G ε₀ ε₁ (tipMinus D (Ja P (a := a)) G ε₀ ε₁) =
      tip P f D G ε₀ ε₁ false := by
  have h := ContinuousMap.congr_fun (DoubleCylinder.homotopyDesc_right
    (SSet.toTop.map (attaching D (Ja P (a := a)) G ε₀))
    (SSet.toTop.map (erase D)) (first_isPushout D (Ja P (a := a)) G ε₀)
    (laurentMap P f D G ε₀ ε₁)
    (ContinuousMap.const _ (tip P f D G ε₀ ε₁ false))
    (nullTrack P f D G ε₀ ε₁ false)) (default : |tipSSet.{u + 1}|)
  exact (map_first P f D G ε₀ ε₁ _).trans
    ((congrArg (firstMap P f D G ε₀ ε₁)
      (realized_right (attaching D (Ja P (a := a)) G ε₀) (erase D) _)).trans h)

/-- The shifted tip remains the prescribed plus tip. -/
theorem map_tipPlus :
    map P f D G ε₀ ε₁ (tipPlus D (Ja P (a := a)) G ε₀ ε₁) =
      tip P f D G ε₀ ε₁ true := by
  have h := ContinuousMap.congr_fun (DoubleCylinder.homotopyDesc_right
    (SSet.toTop.map (secondAttaching D (Ja P (a := a)) G ε₀ ε₁))
    (SSet.toTop.map (erase D)) (second_isPushout D (Ja P (a := a)) G ε₀ ε₁)
    (firstMap P f D G ε₀ ε₁) (ContinuousMap.const _ (tip P f D G ε₀ ε₁ true))
    (secondNull P f D G ε₀ ε₁)) (default : |tipSSet.{u + 1}|)
  exact (congrArg (map P f D G ε₀ ε₁)
    (realized_right (secondAttaching D (Ja P (a := a)) G ε₀ ε₁) (erase D) _)).trans h

end Quillen.PerfectComplexes.CoefficientBassSeedTargetCylinderMap
