/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgePath
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNervePointwiseFamily
public import Quillen.Topology.Prespectrum.HomotopyPushout

/-! Exact set-level evaluation of the four displayed reference cylinders. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
open CutOpenCarrier Quillen.NativePathCells

namespace SetDescent
variable {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z) {B : Type u}
  (l : |Y| → B) (r : |Z| → B) (c : |X| × TopCat.I.{u} → B)
  (h0 : ∀ x, c (x, ULift.up 0) = l (SSet.toTop.map f x))
  (h1 : ∀ x, c (x, ULift.up 1) = r (SSet.toTop.map g x))

include h0 h1 in
theorem square :
    (forget TopCat).map (Quillen.intervalEndpoints |X|) ≫ (↾c) =
      (forget TopCat).map (DoubleCylinder.endMap (SSet.toTop.map f)
        (SSet.toTop.map g)) ≫ (↾(Sum.elim l r)) := by
  apply ConcreteCategory.hom_ext
  intro z
  rcases z with x | x
  · exact h0 x
  · exact h1 x

/-- Descent in Types, with no continuity requirement on native evaluation. -/
def value : |DoubleCylinder.simplicial f g| → B :=
  ((DoubleCylinder.realized_isPushout f g).map (forget TopCat)).desc
    (↾c) (↾(Sum.elim l r)) (square f g l r c h0 h1)

theorem value_cylinder (z : |X| × TopCat.I.{u}) :
    value f g l r c h0 h1 (DoubleCylinder.realizedCylinder f g z) = c z :=
  ConcreteCategory.congr_hom
    (((DoubleCylinder.realized_isPushout f g).map (forget TopCat)).inl_desc
      (↾c) (↾(Sum.elim l r)) (square f g l r c h0 h1)) z

theorem value_ends (z : |Y| ⊕ |Z|) :
    value f g l r c h0 h1 (DoubleCylinder.realizedEnds f g z) = Sum.elim l r z :=
  ConcreteCategory.congr_hom
    (((DoubleCylinder.realized_isPushout f g).map (forget TopCat)).inr_desc
      (↾c) (↾(Sum.elim l r)) (square f g l r c h0 h1)) z

theorem eval_realized_left {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
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

theorem eval_realized_right {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
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


theorem value_left (y : |Y|) :
    value f g l r c h0 h1 (SSet.toTop.map (left f g) y) = l y :=
  (congrArg (value f g l r c h0 h1) (eval_realized_left f g y)).trans
    (value_ends f g l r c h0 h1 (Sum.inl y))

theorem value_right (z : |Z|) :
    value f g l r c h0 h1 (SSet.toTop.map (right f g) z) = r z :=
  (congrArg (value f g l r c h0 h1) (eval_realized_right f g z)).trans
    (value_ends f g l r c h0 h1 (Sum.inr z))
end SetDescent

variable {V W T : Model.{u}} (E : V ⟶ W) (J : W ⟶ T)

/-- The original native homotopy pushout of the two copies of `prespectrumMap J`. -/
abbrev nativeSpan := LoopPrespectrum.HomotopyPushout.prespectrum
  (prespectrumMap J) (prespectrumMap J)

/-- Evaluate the full `E` reference on the original overlap cylinder at the unchanged height `t`. -/
def nativeCylinder (n : ℕ) (y : |parameterSSet E|) (t : I)
    (x : (prespectrum V).space n) : (nativeSpan J).space n :=
  LoopPrespectrum.HomotopyPushout.cylinder (prespectrumMap J) (prespectrumMap J) n
    (t, pointwisePrespectrumFamily E n y x)

/-- Evaluate the full `E ≫ J` reference in the original plus inclusion of the native span. -/
def nativePlus (n : ℕ) (y : |parameterSSet (E ≫ J)|)
    (x : (prespectrum V).space n) : (nativeSpan J).space n :=
  LoopPrespectrum.HomotopyPushout.left (prespectrumMap J) (prespectrumMap J) n
    (pointwisePrespectrumFamily (E ≫ J) n y x)

/-- Evaluate the full `E ≫ J` reference in the original minus inclusion of the native span. -/
def nativeMinus (n : ℕ) (y : |parameterSSet (E ≫ J)|)
    (x : (prespectrum V).space n) : (nativeSpan J).space n :=
  LoopPrespectrum.HomotopyPushout.right (prespectrumMap J) (prespectrumMap J) n
    (pointwisePrespectrumFamily (E ≫ J) n y x)

theorem attachment_native (n : ℕ) (y : |parameterSSet E|)
    (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (E ≫ J) n (SSet.toTop.map (attachment E J) y) x =
      (prespectrumMap J).map n (pointwisePrespectrumFamily E n y x) := by
  obtain ⟨k, N, z, hz⟩ := exists_parameter E y
  rw [← hz]
  change pointwisePrespectrumFamily (E ≫ J) n
    (mapParameter (postcompNode J) (parameter E N z)) x = _
  rw [mapParameter_parameter, pointwisePrespectrumFamily_parameter,
    pointwisePrespectrumFamily_parameter]
  exact prespectrumFamily_postcomp N J n z x

theorem nativeCylinder_zero (n : ℕ) (y : |parameterSSet E|) :
    nativeCylinder E J n y 0 = nativePlus E J n (SSet.toTop.map (attachment E J) y) := by
  funext x
  dsimp only [nativeCylinder, nativePlus]
  rw [LoopPrespectrum.HomotopyPushout.cylinder_zero, attachment_native]

theorem nativeCylinder_one (n : ℕ) (y : |parameterSSet E|) :
    nativeCylinder E J n y 1 = nativeMinus E J n (SSet.toTop.map (attachment E J) y) := by
  funext x
  dsimp only [nativeCylinder, nativeMinus]
  rw [LoopPrespectrum.HomotopyPushout.cylinder_one, attachment_native]

/-- The prescribed edge-one-to-two clock `lower (symm (upper t))`. -/
def time12 (t : I) : I := lower (unitInterval.symm (upper t))
/-- The prescribed edge-zero-to-one clock `lower (symm (lower t))`. -/
def time01 (t : I) : I := lower (unitInterval.symm (lower t))
/-- The prescribed edge-zero-to-three clock `upper (lower t)`. -/
def time03 (t : I) : I := upper (lower t)
/-- The prescribed edge-three-to-four clock `upper (upper t)`. -/
def time34 (t : I) : I := upper (upper t)

@[simp] theorem time12_one : time12 1 = 0 := by
  apply Subtype.ext
  norm_num [time12, lower, upper, unitInterval.symm]
@[simp] theorem time34_one : time34 1 = 1 := by
  apply Subtype.ext
  norm_num [time34, upper]
theorem time01_one : time01 1 = time12 0 := by
  apply Subtype.ext
  norm_num [time01, time12, lower, upper, unitInterval.symm]
theorem time03_zero : time03 0 = time01 0 := by
  apply Subtype.ext
  norm_num [time03, time01, lower, upper, unitInterval.symm]
theorem time34_zero : time34 0 = time03 1 := by
  apply Subtype.ext
  norm_num [time34, time03, lower, upper]

/-- First displayed cylinder: the positive quarter runs towards the positive summand. -/
def firstNativeEval (n : ℕ) :
    |first E J| → (prespectrum V).space n → (nativeSpan J).space n :=
  SetDescent.value (𝟙 _) (attachment E J)
    (fun y ↦ nativeCylinder E J n y (time12 0)) (nativePlus E J n)
    (fun z ↦ nativeCylinder E J n z.1 (time12 z.2.down))
    (fun y ↦ congrArg (fun z ↦ nativeCylinder E J n z (time12 0))
      (ConcreteCategory.congr_hom (SSet.toTop.map_id (parameterSSet E)) y).symm)
    (fun y ↦ by rw [time12_one]; exact nativeCylinder_zero E J n y)

theorem firstNativeEval_one (n : ℕ) (y : |parameterSSet E|) :
    firstNativeEval E J n (SSet.toTop.map (firstOne E J) y) =
      nativeCylinder E J n y (time12 0) :=
  SetDescent.value_left _ _ _ _ _ _ _ y

theorem firstNativeEval_plus (n : ℕ) (y : |parameterSSet (E ≫ J)|) :
    firstNativeEval E J n (SSet.toTop.map (firstPlus E J) y) = nativePlus E J n y :=
  SetDescent.value_right _ _ _ _ _ _ _ y

/-- Second displayed cylinder: midpoint to the positive quarter. -/
def secondNativeEval (n : ℕ) :
    |second E J| → (prespectrum V).space n → (nativeSpan J).space n :=
  SetDescent.value (𝟙 _) (firstOne E J)
    (fun y ↦ nativeCylinder E J n y (time01 0)) (firstNativeEval E J n)
    (fun z ↦ nativeCylinder E J n z.1 (time01 z.2.down))
    (fun y ↦ congrArg (fun z ↦ nativeCylinder E J n z (time01 0))
      (ConcreteCategory.congr_hom (SSet.toTop.map_id (parameterSSet E)) y).symm)
    (fun y ↦ by rw [time01_one]; exact (firstNativeEval_one E J n y).symm)

theorem secondNativeEval_zero (n : ℕ) (y : |parameterSSet E|) :
    secondNativeEval E J n (SSet.toTop.map (secondZero E J) y) =
      nativeCylinder E J n y (time01 0) :=
  SetDescent.value_left _ _ _ _ _ _ _ y

theorem secondNativeEval_first (n : ℕ) (y : |first E J|) :
    secondNativeEval E J n (SSet.toTop.map (firstInSecond E J) y) =
      firstNativeEval E J n y :=
  SetDescent.value_right _ _ _ _ _ _ _ y

/-- Third displayed cylinder: midpoint to the negative quarter. -/
def thirdNativeEval (n : ℕ) :
    |third E J| → (prespectrum V).space n → (nativeSpan J).space n :=
  SetDescent.value (secondZero E J) (𝟙 _)
    (secondNativeEval E J n) (fun y ↦ nativeCylinder E J n y (time03 1))
    (fun z ↦ nativeCylinder E J n z.1 (time03 z.2.down))
    (fun y ↦ by rw [time03_zero]; exact (secondNativeEval_zero E J n y).symm)
    (fun y ↦ congrArg (fun z ↦ nativeCylinder E J n z (time03 1))
      (ConcreteCategory.congr_hom (SSet.toTop.map_id (parameterSSet E)) y).symm)

theorem thirdNativeEval_second (n : ℕ) (y : |second E J|) :
    thirdNativeEval E J n (SSet.toTop.map (secondInThird E J) y) =
      secondNativeEval E J n y :=
  SetDescent.value_left _ _ _ _ _ _ _ y

theorem thirdNativeEval_three (n : ℕ) (y : |parameterSSet E|) :
    thirdNativeEval E J n (SSet.toTop.map (thirdThree E J) y) =
      nativeCylinder E J n y (time03 1) :=
  SetDescent.value_right _ _ _ _ _ _ _ y

/-- Actual evaluation of the entire four-edge tree, by its fourth displayed pushout. -/
def nativeEval (n : ℕ) : space E J → (prespectrum V).space n → (nativeSpan J).space n :=
  SetDescent.value (thirdThree E J) (attachment E J)
    (thirdNativeEval E J n) (nativeMinus E J n)
    (fun z ↦ nativeCylinder E J n z.1 (time34 z.2.down))
    (fun y ↦ by rw [time34_zero]; exact (thirdNativeEval_three E J n y).symm)
    (fun y ↦ by rw [time34_one]; exact nativeCylinder_one E J n y)

theorem nativeEval_third (n : ℕ) (y : |third E J|) :
    nativeEval E J n (SSet.toTop.map (thirdInTree E J) y) = thirdNativeEval E J n y :=
  SetDescent.value_left _ _ _ _ _ _ _ y

theorem nativeEval_minus (n : ℕ) (y : |parameterSSet (E ≫ J)|) :
    nativeEval E J n (SSet.toTop.map (minusVertex E J) y) = nativeMinus E J n y :=
  SetDescent.value_right _ _ _ _ _ _ _ y

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
