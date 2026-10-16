/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.OpenGluing.Binary

/-! # Genuine target-map descent from an original overlap homotopy -/
@[expose] public section

open Quillen.CochainComplex


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.OpenHomotopyGluing
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (j : U ⟶ X) (k : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion j] [IsOpenImmersion k]
  (h : a ≫ j = b ≫ k)
  {K : CochainComplex W.Modules ℤ} {A : CochainComplex U.Modules ℤ} {B : CochainComplex V.Modules ℤ}
    {L : CochainComplex X.Modules ℤ}
  (α : K ⟶ (restrict a).obj A) (β : K ⟶ (restrict b).obj B)
  (p : A ⟶ (restrict j).obj L) (q : B ⟶ (restrict k).obj L)

/-- The genuine mate/counit identity retains the actual right target composite. -/
theorem right_target_local_eq :
    ((extensionByZero a).map β ≫ (extensionByZeroBaseChange b a k j h.symm).app B) ≫
      (restrict j).map (extensionByZeroMap k q) =
    extensionByZeroMap a (β ≫ (restrict b).map q ≫
      (openSquareRestrictIso b a k j h.symm).hom.app L) := by
  rw [extensionByZeroMap_eq k q, Functor.map_comp]
  simp only [Category.assoc]
  have hn := (extensionByZeroBaseChange b a k j h.symm).naturality q
  change (extensionByZero a).map ((restrict b).map q) ≫
      (extensionByZeroBaseChange b a k j h.symm).app ((restrict k).obj L) =
    (extensionByZeroBaseChange b a k j h.symm).app B ≫
      (restrict j).map ((extensionByZero k).map q) at hn
  rw [← Category.assoc ((extensionByZeroBaseChange b a k j h.symm).app B), ← hn,
    Category.assoc, extensionByZeroBaseChange_counit]
  simp only [extensionByZeroMap_eq, Functor.map_comp, Category.assoc]

/-- Original left overlap/target composition is the double actual adjoint. -/
theorem left_target_eq :
    left a j α ≫ extensionByZeroMap j p =
    extensionByZeroMap j (extensionByZeroMap a (α ≫ (restrict a).map p)) := by
  rw [left, extensionByZeroMap_precomp, extensionByZeroMap_postcomp]

/-- Original right overlap/target composition is the other double actual adjoint. -/
theorem right_target_eq :
    right a b j k h β ≫ extensionByZeroMap k q =
    extensionByZeroMap j (extensionByZeroMap a (β ≫ (restrict b).map q ≫
      (openSquareRestrictIso b a k j h.symm).hom.app L)) := by
  rw [right, extensionByZeroMap_postcomp, right_target_local_eq a b j k h β q]

variable (H : Homotopy (α ≫ (restrict a).map p)
  (β ≫ (restrict b).map q ≫ (openSquareRestrictIso b a k j h.symm).hom.app L))

/-- The specified original local overlap homotopy gives a genuine global overlap homotopy. -/
def targetHomotopy : Homotopy (left a j α ≫ extensionByZeroMap j p)
    (right a b j k h β ≫ extensionByZeroMap k q) :=
  (Homotopy.ofEq (left_target_eq a j α p)).trans
    ((extensionByZeroMapHomotopy j (extensionByZeroMapHomotopy a H)).trans
      (Homotopy.ofEq (right_target_eq a b j k h β q).symm))

/-- The actual global chain map descended from the given local maps and overlap homotopy. -/
def desc : glued a b j k h α β ⟶ L :=
  homotopyPushoutDesc (left a j α) (right a b j k h β)
    (extensionByZeroMap j p) (extensionByZeroMap k q) (targetHomotopy a b j k h α β p q H)

/-- The first original local map is recovered strictly after actual restriction. -/
@[reassoc (attr := simp)]
theorem first_desc :
    first a b j k h α β ≫ (restrict j).map (desc a b j k h α β p q H) = p := by
  unfold first desc
  rw [Category.assoc, ← Functor.map_comp, homotopyPushoutInl_desc, extensionByZeroMap_restrict]

/-- The second original local map is recovered strictly after actual restriction. -/
@[reassoc (attr := simp)]
theorem second_desc :
    second a b j k h α β ≫ (restrict k).map (desc a b j k h α β p q H) = q := by
  unfold second desc
  rw [Category.assoc, ← Functor.map_comp, homotopyPushoutInr_desc, extensionByZeroMap_restrict]

/-- Weak original first local target maps give weak original restricted descent. -/
theorem desc_restrict_first_quasiIso
    (hc : ∀ x : U, j x ∈ Set.range k → x ∈ Set.range a)
    [QuasiIso β] [QuasiIso p] : QuasiIso ((restrict j).map (desc a b j k h α β p q H)) := by
  have := first_quasiIso a b j k h α β hc
  have : QuasiIso (first a b j k h α β ≫ (restrict j).map (desc a b j k h α β p q H)) := by
    rw [first_desc]
    infer_instance
  exact (quasiIso_iff_comp_left _ _).mp this

/-- Symmetric restricted descent, with no weakness premise on the other local target map. -/
theorem desc_restrict_second_quasiIso
    (hc : ∀ x : V, k x ∈ Set.range j → x ∈ Set.range b)
    [QuasiIso α] [QuasiIso q] : QuasiIso ((restrict k).map (desc a b j k h α β p q H)) := by
  have := second_quasiIso a b j k h α β hc
  have : QuasiIso (second a b j k h α β ≫ (restrict k).map (desc a b j k h α β p q H)) := by
    rw [second_desc]
    infer_instance
  exact (quasiIso_iff_comp_left _ _).mp this

end Quillen.PerfectComplexes.OpenHomotopyGluing
