/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeTargetChartAttachment
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassNegativeTargetFirstMap
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeEvaluation

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
namespace Quillen.PerfectComplexes.CoefficientBassNegativeTargetSingleSheet
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
  (ε : G.functor ≅ (D ≫ Ja P (a := a)).functor)

/-- The realized first target sheet for the negative chart and the transported anchor `ε`. -/
abbrev targetSpace := |firstSimplicial (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
  (targetAnchor P f D G ε)|
/-- The inclusion of the target Laurent parameter space into the single target sheet. -/
abbrev targetLaurent : C(|parameterSSet (G ≫ L P f)|, targetSpace P f D G ε) :=
  (SSet.toTop.map (left₀ (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
    (targetAnchor P f D G ε))).hom
/-- The map of polynomial parameter spaces induced by postcomposition with `M P f`. -/
def polynomialMap := mapParameter (postcompNode (M P f) (F := D))
/-- The Laurent parameter map followed by inclusion in the single target sheet. -/
def laurentMap : C(|parameterSSet G|, targetSpace P f D G ε) :=
  (targetLaurent P f D G ε).comp (mapParameter (postcompNode (L P f)))

/-- The common source anchor `ε`, independent of the Boolean sheet label. -/
abbrev sheetAnchor (_e : Bool) := ε

/-- The unique chosen tip of the target sheet, independent of the Boolean sheet label. -/
def tip (_e : Bool) : targetSpace P f D G ε :=
  SSet.toTop.map (right₀ (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
    (targetAnchor P f D G ε)) (default : |tipSSet.{u+1}|)

/-- The target-sheet cylinder, using the same map for both Boolean sheet labels. -/
def cylinder (_e : Bool) : C(|parameterSSet (D ≫ M P f)| × I,
    targetSpace P f D G ε) :=
  ⟨fun z ↦ DoubleCylinder.realizedCylinder
    (attaching (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f) (targetAnchor P f D G ε))
    (erase (D ≫ M P f)) (z.1, ULift.up z.2), by fun_prop⟩

private theorem parameter_comp {V₀ W₀ V₁ W₁ V₂ W₂ : Model.{v}}
    {F₀ : V₀ ⟶ W₀} {F₁ : V₁ ⟶ W₁} {F₂ : V₂ ⟶ W₂}
    (g : Node F₀ → Node F₁) (h : Node F₁ → Node F₂) (y : |parameterSSet F₀|) :
    mapParameter h (mapParameter g y) = mapParameter (fun N ↦ h (g N)) y := by
  obtain ⟨k, N, z, rfl⟩ := exists_parameter F₀ y
  rw [mapParameter_parameter, mapParameter_parameter, mapParameter_parameter]

/-- The route through the source attachment and Laurent map into the target sheet. -/
abbrev startMap (e : Bool) := (laurentMap P f D G ε).comp
  (mapParameter (attachPostcompNode D (Ja P (a := a)) G (sheetAnchor P D G ε e)))
/-- The route through the polynomial map and target attachment into the target sheet. -/
abbrev middleMap (e : Bool) := (targetLaurent P f D G ε).comp
  ((mapParameter (attachPostcompNode (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
    (targetAnchor P f D G (sheetAnchor P D G ε e)))).comp (polynomialMap P f D))

/-- The full original chart square runs before the target polynomial contraction. -/
def chartTrack (e : Bool) : (startMap P f D G ε e).Homotopy
    (middleMap P f D G ε e) where
  toFun z := targetLaurent P f D G ε
    (moving P f D G (sheetAnchor P D G ε e) (z.2, z.1))
  continuous_toFun := by fun_prop
  map_zero_left y := by
    rw [moving_zero_attachment]
    exact congrArg (targetLaurent P f D G ε) (parameter_comp _ _ y).symm
  map_one_left y := by
    rw [moving_one_attachment]
    exact congrArg (targetLaurent P f D G ε) (parameter_comp _ _ y).symm

/-- The second half uses the literal target sheet and its own tip. -/
def contraction (e : Bool) : (middleMap P f D G ε e).Homotopy
    (ContinuousMap.const _ (tip P f D G ε e)) where
  toFun z := cylinder P f D G ε e (polynomialMap P f D z.2, z.1)
  continuous_toFun := by fun_prop
  map_zero_left y := by
    have h := ConcreteCategory.congr_hom
      (first_isPushout (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
        (targetAnchor P f D G ε)).w (Sum.inl (polynomialMap P f D y))
    exact h.trans (FourEdgeTree.SetDescent.eval_realized_left _ _ _).symm
  map_one_left y := by
    have h := ConcreteCategory.congr_hom
      (first_isPushout (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
        (targetAnchor P f D G ε)).w (Sum.inr (polynomialMap P f D y))
    exact h.trans ((FourEdgeTree.SetDescent.eval_realized_right _ _ _).symm.trans
      (congrArg (SSet.toTop.map (right₀ (D ≫ M P f) (Jb P (b := b)) (G ≫ L P f)
        (targetAnchor P f D G ε))) (Subsingleton.elim _ _)))

/-- Both half clocks are the original cone-map null word, rather than a direct target cylinder. -/
def nullTrack (e : Bool) :=
  (chartTrack P f D G ε e).trans (contraction P f D G ε e)

/-- The first genuine displayed pushout descends the prescribed ordinary null track. -/
def firstMap : C(|firstSimplicial D (Ja P (a := a)) G ε|,
    targetSpace P f D G ε) :=
  DoubleCylinder.homotopyDesc
    (SSet.toTop.map (attaching D (Ja P (a := a)) G ε)) (SSet.toTop.map (erase D))
    (first_isPushout D (Ja P (a := a)) G ε) (laurentMap P f D G ε)
    (ContinuousMap.const _ (tip P f D G ε false)) (nullTrack P f D G ε false)


/-- The first descent retains the full Laurent map, including its reference anchors. -/
theorem firstMap_laurent (y : |parameterSSet G|) :
    firstMap P f D G ε (SSet.toTop.map (left₀ D (Ja P (a := a)) G ε) y) =
      laurentMap P f D G ε y := by
  have h := ContinuousMap.congr_fun (DoubleCylinder.homotopyDesc_left
    (SSet.toTop.map (attaching D (Ja P (a := a)) G ε))
    (SSet.toTop.map (erase D)) (first_isPushout D (Ja P (a := a)) G ε)
    (laurentMap P f D G ε)
    (ContinuousMap.const _ (tip P f D G ε false))
    (nullTrack P f D G ε false)) y
  exact (congrArg (firstMap P f D G ε)
    (realized_left (attaching D (Ja P (a := a)) G ε) (erase D) y)).trans h

/-- The first-sheet cylinder retains both literal original half clocks. -/
theorem firstMap_cylinder (y : |parameterSSet D|) (t : I) :
    firstMap P f D G ε
      (DoubleCylinder.realizedCylinder
        (attaching D (Ja P (a := a)) G ε) (erase D) (y, ULift.up t)) =
      nullTrack P f D G ε false (t, y) :=
  DoubleCylinder.homotopyDesc_apply_cylinder
    (SSet.toTop.map (attaching D (Ja P (a := a)) G ε))
    (SSet.toTop.map (erase D)) (first_isPushout D (Ja P (a := a)) G ε)
    (laurentMap P f D G ε)
    (ContinuousMap.const _ (tip P f D G ε false))
    (nullTrack P f D G ε false) t y

end Quillen.PerfectComplexes.CoefficientBassNegativeTargetSingleSheet
