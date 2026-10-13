/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.UnitSections
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # Original scalar multiplication and structure-module pushforward

The original structure-module map intertwines multiplication by original global sections.
A section in the actual ring-map kernel gives a zero composite of the actual sheaf maps.
-/
@[expose] public section

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.SchemeSheaf
/-- The actual structure-module map intertwines original global scalar multiplication. -/
theorem unitMul_unitToPushforward {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Γ(Y, ⊤)) :
    unitMul Y s ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward f).map (unitMul X (f.appTop.hom s)) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change Γ(Y, U) at x
  change (f.app U).hom (x * (Y.presheaf.map (homOfLE le_top).op).hom s) =
    (f.app U).hom x * (X.presheaf.map (homOfLE le_top).op).hom (f.appTop.hom s)
  rw [map_mul]
  congr 1
  have h : Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ f.app U =
      f.appTop ≫ X.presheaf.map (homOfLE le_top).op := by
    simp only [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE,
      Scheme.Hom.appLE_map]
  exact congrArg (fun k => CommRingCat.Hom.hom k s) h
/-- Multiplication by the zero global section is the actual zero sheaf map. -/
theorem unitMul_zero (X : Scheme.{u}) : unitMul X 0 = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change Γ(X, U) at x
  change x * (X.presheaf.map (homOfLE le_top).op).hom 0 = 0
  simp
/-- A scalar in the actual global ring-map kernel gives the original zero composite. -/
theorem unitMul_unitToPushforward_zero {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Γ(Y, ⊤))
    (hs : f.appTop.hom s = 0) :
    unitMul Y s ≫ SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom = 0 := by
  rw [unitMul_unitToPushforward, hs, unitMul_zero, Functor.map_zero, comp_zero]
end Quillen.SchemeSheaf
