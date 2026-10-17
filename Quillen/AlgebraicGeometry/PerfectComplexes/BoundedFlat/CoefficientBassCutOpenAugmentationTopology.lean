/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCutOpenAugmentation

/-! The added original sheets retain distinct tips and the displayed contractible realization. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenAugmentation
open CutOpenCarrier
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


variable {V W T : Model.{u}} (F : V ⟶ W) (J : W ⟶ T) (G : V ⟶ T)
  (ε₀ ε₁ : G.functor ≅ (F ≫ J).functor) (B : SSet.{u}) (j : parameterSSet G ⟶ B)

/-- The realization of the base `B` with both cut-open polynomial sheets attached along `j`. -/
abbrev space : TopCat.{u} := |simplicial F J G ε₀ ε₁ B j|
/-- The continuous map from the cut-open carrier to its augmentation over `B`. -/
def continuousMap : C(CutOpenCarrier.space F J G ε₀ ε₁, space F J G ε₀ ε₁ B j) :=
  (SSet.toTop.map (map F J G ε₀ ε₁ B j)).hom

/-- The tip of the first attached polynomial sheet in the augmented realization. -/
def tipMinus : space F J G ε₀ ε₁ B j :=
  SSet.toTop.map (firstIn F J G ε₀ ε₁ B j)
    (SSet.toTop.map (firstTip F J G ε₀ B j) (default : |tipSSet.{u}|))
/-- The tip of the second attached polynomial sheet in the augmented realization. -/
def tipPlus : space F J G ε₀ ε₁ B j :=
  SSet.toTop.map (secondTip F J G ε₀ ε₁ B j) (default : |tipSSet.{u}|)

/-- The second-sheet cylinder height, equal to zero on the first-stage realization. -/
def height : C(space F J G ε₀ ε₁ B j, I) :=
  DoubleCylinder.height (SSet.toTop.map (secondAttaching F J G ε₀ ε₁ B j))
    (SSet.toTop.map (erase F)) (DoubleCylinder.realized_isPushout _ _)

@[simp] theorem height_tipMinus :
    height F J G ε₀ ε₁ B j (tipMinus F J G ε₀ ε₁ B j) = 0 := by
  exact (congrArg (height F J G ε₀ ε₁ B j)
    (realized_left (secondAttaching F J G ε₀ ε₁ B j) (erase F)
      (SSet.toTop.map (firstTip F J G ε₀ B j) default))).trans
    (DoubleCylinder.height_left _ _ _ _)

@[simp] theorem height_tipPlus :
    height F J G ε₀ ε₁ B j (tipPlus F J G ε₀ ε₁ B j) = 1 := by
  exact (congrArg (height F J G ε₀ ε₁ B j)
    (realized_right (secondAttaching F J G ε₀ ε₁ B j) (erase F) default)).trans
    (DoubleCylinder.height_right _ _ _ _)

theorem tips_ne : tipMinus F J G ε₀ ε₁ B j ≠ tipPlus F J G ε₀ ε₁ B j := by
  intro h
  have hh := congrArg (height F J G ε₀ ε₁ B j) h
  rw [height_tipMinus, height_tipPlus] at hh
  exact zero_ne_one hh

@[simp] theorem continuousMap_tipMinus :
    continuousMap F J G ε₀ ε₁ B j (CutOpenCarrier.tipMinus F J G ε₀ ε₁) =
      tipMinus F J G ε₀ ε₁ B j := by
  have h := congrArg (fun k ↦ SSet.toTop.map k (default : |tipSSet.{u}|))
    (map_tipMinus F J G ε₀ ε₁ B j)
  simpa only [Functor.map_comp, TopCat.comp_app, continuousMap,
    CutOpenCarrier.tipMinus, tipMinus] using h

@[simp] theorem continuousMap_tipPlus :
    continuousMap F J G ε₀ ε₁ B j (CutOpenCarrier.tipPlus F J G ε₀ ε₁) =
      tipPlus F J G ε₀ ε₁ B j := by
  have h := congrArg (fun k ↦ SSet.toTop.map k (default : |tipSSet.{u}|))
    (map_tipPlus F J G ε₀ ε₁ B j)
  simpa only [Functor.map_comp, TopCat.comp_app, continuousMap,
    CutOpenCarrier.tipPlus, tipPlus] using h

/-- The whole Laurent summand enters through its prescribed map to the base. -/
def laurentInclusion : C(|parameterSSet G|, space F J G ε₀ ε₁ B j) :=
  (SSet.toTop.map (j ≫ baseIn F J G ε₀ ε₁ B j)).hom

/-- The added ordinary cylinder keeps its original interval coordinate. -/
def cylinderMinus : C(|parameterSSet F| × I, space F J G ε₀ ε₁ B j) :=
  ⟨fun z ↦ SSet.toTop.map (firstIn F J G ε₀ ε₁ B j)
    (DoubleCylinder.realizedCylinder (attaching F J G ε₀ ≫ j) (erase F)
      (z.1, ULift.up z.2)), by fun_prop⟩

/-- The added shifted cylinder keeps the same independent interval coordinate. -/
def cylinderPlus : C(|parameterSSet F| × I, space F J G ε₀ ε₁ B j) :=
  ⟨fun z ↦ DoubleCylinder.realizedCylinder (secondAttaching F J G ε₀ ε₁ B j) (erase F)
    (z.1, ULift.up z.2), by fun_prop⟩

private theorem realized_changeLeft {X Y Y' Z : SSet.{u}}
    (f : X ⟶ Y) (f' : X ⟶ Y') (g : X ⟶ Z) (k : Y ⟶ Y') (h : f ≫ k = f') :
    DoubleCylinder.realizedCylinder f g ≫ SSet.toTop.map (changeLeft f f' g k h) =
      DoubleCylinder.realizedCylinder f' g := by
  dsimp only [DoubleCylinder.realizedCylinder]
  rw [Category.assoc, ← Functor.map_comp, changeLeft_cylinder]

@[simp] theorem continuousMap_laurent (x : |parameterSSet G|) :
    continuousMap F J G ε₀ ε₁ B j (CutOpenCarrier.laurentInclusion F J G ε₀ ε₁ x) =
      laurentInclusion F J G ε₀ ε₁ B j x := by
  have h := congrArg (fun k ↦ SSet.toTop.map k x) (map_laurent F J G ε₀ ε₁ B j)
  simpa only [Functor.map_comp, TopCat.comp_app, continuousMap,
    CutOpenCarrier.laurentInclusion, laurentInclusion, ContinuousMap.comp_apply] using h

@[simp] theorem continuousMap_cylinderMinus (x : |parameterSSet F|) (t : I) :
    continuousMap F J G ε₀ ε₁ B j (CutOpenCarrier.cylinderMinus F J G ε₀ ε₁ (x, t)) =
      cylinderMinus F J G ε₀ ε₁ B j (x, t) := by
  have h := congrArg (fun k ↦ SSet.toTop.map k
    (DoubleCylinder.realizedCylinder (attaching F J G ε₀) (erase F) (x, ULift.up t)))
    (map_first F J G ε₀ ε₁ B j)
  have hc := ConcreteCategory.congr_hom
    (realized_changeLeft (attaching F J G ε₀) (attaching F J G ε₀ ≫ j)
      (erase F) j rfl) (x, ULift.up t)
  simp only [Functor.map_comp, TopCat.comp_app, firstMap] at h hc
  exact h.trans (congrArg (SSet.toTop.map (firstIn F J G ε₀ ε₁ B j)) hc)

@[simp] theorem continuousMap_cylinderPlus (x : |parameterSSet F|) (t : I) :
    continuousMap F J G ε₀ ε₁ B j (CutOpenCarrier.cylinderPlus F J G ε₀ ε₁ (x, t)) =
      cylinderPlus F J G ε₀ ε₁ B j (x, t) :=
  ConcreteCategory.congr_hom
    (realized_changeLeft (CutOpenCarrier.secondAttaching F J G ε₀ ε₁)
      (secondAttaching F J G ε₀ ε₁ B j) (erase F) (firstMap F J G ε₀ B j)
      (by
        dsimp only [CutOpenCarrier.secondAttaching, secondAttaching]
        rw [Category.assoc, firstMap_left])) (x, ULift.up t)

private theorem parameter_contractible {V W : Model.{u}} (F : V ⟶ W) :
    ContractibleSpace |parameterSSet F| :=
  (contractible_iff_id_nullhomotopic _).2
    ⟨classifyingSpacePoint (referenceNode F), ⟨(referenceContraction F).symm⟩⟩

/-- The base is retained and each actual sheet is attached by its displayed pushout. -/
theorem contractibleSpace [ContractibleSpace |B|] :
    ContractibleSpace (space F J G ε₀ ε₁ B j) := by
  let : ContractibleSpace |parameterSSet F| := parameter_contractible F
  let : ContractibleSpace |first F J G ε₀ B j| :=
    DoubleCylinder.contractibleSpace_of_contractible
      (SSet.toTop.map (attaching F J G ε₀ ≫ j)) (SSet.toTop.map (erase F))
      (DoubleCylinder.realized_isPushout _ _)
  exact DoubleCylinder.contractibleSpace_of_contractible
    (SSet.toTop.map (secondAttaching F J G ε₀ ε₁ B j)) (SSet.toTop.map (erase F))
    (DoubleCylinder.realized_isPushout _ _)

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.CutOpenAugmentation
