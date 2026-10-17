/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeEvaluation

/-! All four original cell values and the whole overlap value of native span evaluation. -/
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
/-- The two displayed pushout legs determine every set-level value. -/
theorem SetDescent.funext {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : X ⟶ Z)
    {B : Type u} (a b : |DoubleCylinder.simplicial f g| → B)
    (hc : ∀ z, a (DoubleCylinder.realizedCylinder f g z) =
      b (DoubleCylinder.realizedCylinder f g z))
    (hl : ∀ y, a (SSet.toTop.map (left f g) y) = b (SSet.toTop.map (left f g) y))
    (hr : ∀ z, a (SSet.toTop.map (right f g) z) = b (SSet.toTop.map (right f g) z)) :
    a = b := by
  have h : (↾a) = (↾b) :=
    ((DoubleCylinder.realized_isPushout f g).map (forget TopCat)).hom_ext
      (by apply ConcreteCategory.hom_ext; exact hc)
      (by
        apply ConcreteCategory.hom_ext
        intro z
        change a (DoubleCylinder.realizedEnds f g z) = b (DoubleCylinder.realizedEnds f g z)
        rcases z with y | z
        · rw [← SetDescent.eval_realized_left]
          exact hl y
        · rw [← SetDescent.eval_realized_right]
          exact hr z)
  exact _root_.funext (fun z ↦ ConcreteCategory.congr_hom h z)

theorem realized_comp {X Y Z : SSet.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : |X|) :
    SSet.toTop.map (f ≫ g) x = SSet.toTop.map g (SSet.toTop.map f x) :=
  ConcreteCategory.congr_hom (SSet.toTop.map_comp f g) x

theorem realizedEdge_comp {X Y Z : SSet.{u}} (H : X ⊗ Δ[1] ⟶ Y) (g : Y ⟶ Z)
    (z : |X| × I) :
    realizedEdge (H ≫ g) z = SSet.toTop.map g (realizedEdge H z) :=
  realized_comp H g _

variable {V W T : Model.{u}} (E : V ⟶ W) (J : W ⟶ T)

theorem nativeEval_second (n : ℕ) (y : |second E J|) :
    nativeEval E J n (SSet.toTop.map (secondInTree E J) y) = secondNativeEval E J n y := by
  rw [secondInTree, realized_comp]
  rw [nativeEval_third, thirdNativeEval_second]

theorem nativeEval_first (n : ℕ) (y : |first E J|) :
    nativeEval E J n (SSet.toTop.map (firstInTree E J) y) = firstNativeEval E J n y := by
  rw [firstInTree, realized_comp]
  rw [nativeEval_second, secondNativeEval_first]

theorem nativeEval_plus (n : ℕ) (y : |parameterSSet (E ≫ J)|) :
    nativeEval E J n (SSet.toTop.map (plusVertex E J) y) = nativePlus E J n y := by
  rw [plusVertex, realized_comp]
  rw [nativeEval_first, firstNativeEval_plus]

theorem nativeEval_edge12 (n : ℕ) (y : |parameterSSet E|) (t : I)
    (x : (prespectrum V).space n) :
    nativeEval E J n (realizedEdge (edge12 E J) (y,t)) x =
      nativeCylinder E J n y (time12 t) x := by
  rw [edge12, realizedEdge_comp]
  change nativeEval E J n (SSet.toTop.map (firstInTree E J)
    (DoubleCylinder.realizedCylinder (𝟙 _) (attachment E J) (y, ULift.up t))) x = _
  rw [nativeEval_first]
  exact congrFun (SetDescent.value_cylinder _ _ _ _ _ _ _ (y, ULift.up t)) x

theorem nativeEval_edge01 (n : ℕ) (y : |parameterSSet E|) (t : I)
    (x : (prespectrum V).space n) :
    nativeEval E J n (realizedEdge (edge01 E J) (y,t)) x =
      nativeCylinder E J n y (time01 t) x := by
  rw [edge01, realizedEdge_comp]
  change nativeEval E J n (SSet.toTop.map (secondInTree E J)
    (DoubleCylinder.realizedCylinder (𝟙 _) (firstOne E J) (y, ULift.up t))) x = _
  rw [nativeEval_second]
  exact congrFun (SetDescent.value_cylinder _ _ _ _ _ _ _ (y, ULift.up t)) x

theorem nativeEval_edge03 (n : ℕ) (y : |parameterSSet E|) (t : I)
    (x : (prespectrum V).space n) :
    nativeEval E J n (realizedEdge (edge03 E J) (y,t)) x =
      nativeCylinder E J n y (time03 t) x := by
  rw [edge03, realizedEdge_comp]
  change nativeEval E J n (SSet.toTop.map (thirdInTree E J)
    (DoubleCylinder.realizedCylinder (secondZero E J) (𝟙 _) (y, ULift.up t))) x = _
  rw [nativeEval_third]
  exact congrFun (SetDescent.value_cylinder _ _ _ _ _ _ _ (y, ULift.up t)) x

theorem nativeEval_edge34 (n : ℕ) (y : |parameterSSet E|) (t : I)
    (x : (prespectrum V).space n) :
    nativeEval E J n (realizedEdge (edge34 E J) (y,t)) x =
      nativeCylinder E J n y (time34 t) x := by
  change nativeEval E J n
    (DoubleCylinder.realizedCylinder (thirdThree E J) (attachment E J) (y, ULift.up t)) x = _
  exact congrFun (SetDescent.value_cylinder _ _ _ _ _ _ _ (y, ULift.up t)) x

theorem overlap_quarter12 (y : |parameterSSet E|) (t : I) :
    overlap E J (y, lower (unitInterval.symm (upper t))) = realizedEdge (edge12 E J) (y,t) := by
  change (((path01 E J y).trans (path12 E J y)).symm.trans
    ((path03 E J y).trans (path34 E J y))) (lower (unitInterval.symm (upper t))) = _
  rw [path_lower]
  change ((path01 E J y).trans (path12 E J y))
    (unitInterval.symm (unitInterval.symm (upper t))) = _
  rw [unitInterval.symm_symm]
  exact path_upper _ _ t

theorem overlap_quarter01 (y : |parameterSSet E|) (t : I) :
    overlap E J (y, lower (unitInterval.symm (lower t))) = realizedEdge (edge01 E J) (y,t) := by
  change (((path01 E J y).trans (path12 E J y)).symm.trans
    ((path03 E J y).trans (path34 E J y))) (lower (unitInterval.symm (lower t))) = _
  rw [path_lower]
  change ((path01 E J y).trans (path12 E J y))
    (unitInterval.symm (unitInterval.symm (lower t))) = _
  rw [unitInterval.symm_symm]
  exact path_lower _ _ t

theorem overlap_quarter03 (y : |parameterSSet E|) (t : I) :
    overlap E J (y, upper (lower t)) = realizedEdge (edge03 E J) (y,t) := by
  change (((path01 E J y).trans (path12 E J y)).symm.trans
    ((path03 E J y).trans (path34 E J y))) (upper (lower t)) = _
  rw [path_upper]
  exact path_lower _ _ t

theorem overlap_quarter34 (y : |parameterSSet E|) (t : I) :
    overlap E J (y, upper (upper t)) = realizedEdge (edge34 E J) (y,t) := by
  change (((path01 E J y).trans (path12 E J y)).symm.trans
    ((path03 E J y).trans (path34 E J y))) (upper (upper t)) = _
  rw [path_upper]
  exact path_upper _ _ t

/-- The literal original four-quarter overlap evaluates at its unchanged whole time. -/
theorem nativeEval_overlap (n : ℕ) (y : |parameterSSet E|) (s : I)
    (x : (prespectrum V).space n) :
    nativeEval E J n (overlap E J (y,s)) x = nativeCylinder E J n y s x := by
  rcases cover s with ⟨u, rfl⟩ | ⟨u, rfl⟩
  · rcases cover (unitInterval.symm u) with ⟨t, ht⟩ | ⟨t, ht⟩
    · have hu : u = unitInterval.symm (lower t) := by
        rw [ht, unitInterval.symm_symm]
      rw [hu, overlap_quarter01, nativeEval_edge01]
      rfl
    · have hu : u = unitInterval.symm (upper t) := by
        rw [ht, unitInterval.symm_symm]
      rw [hu, overlap_quarter12, nativeEval_edge12]
      rfl
  · rcases cover u with ⟨t, rfl⟩ | ⟨t, rfl⟩
    · rw [overlap_quarter03, nativeEval_edge03]
      rfl
    · rw [overlap_quarter34, nativeEval_edge34]
      rfl

end Quillen.Waldhausen.IteratedS.CommonReferenceNerve.FourEdgeTree
