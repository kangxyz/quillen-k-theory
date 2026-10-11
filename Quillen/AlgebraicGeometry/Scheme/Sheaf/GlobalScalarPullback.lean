/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.GlobalUnit

/-! Original global scalar multiplication commutes with geometric sheaf pullback. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace Quillen.SchemeSheaf

/-- Pushforward retains multiplication by the original global scalar under restriction of scalars.
-/
lemma globalScalar_pushforward {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : Γ(Y, ⊤)) (M : X.Modules) :
    (globalScalar Y r).app ((Scheme.Modules.pushforward f).obj M) =
      (Scheme.Modules.pushforward f).map ((globalScalar X (f.appTop r)).app M) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  let m' : M.val.obj (op (f ⁻¹ᵁ U.unop)) := m
  let : Module (Γ(X, f ⁻¹ᵁ U.unop)) (M.val.obj (op (f ⁻¹ᵁ U.unop))) :=
    inferInstanceAs (Module (X.ringCatSheaf.obj.obj (op (f ⁻¹ᵁ U.unop)))
      (M.val.obj (op (f ⁻¹ᵁ U.unop))))
  change (f.app U.unop) (Y.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r) • m' =
    X.presheaf.map (homOfLE (show f ⁻¹ᵁ U.unop ≤ ⊤ from le_top)).op (f.appTop r) • m'
  congr 1
  exact ConcreteCategory.congr_hom (f.naturality
    (homOfLE (show U.unop ≤ ⊤ from le_top)).op) r

/-- Geometric pullback maps the original scalar to its pulled-back scalar. -/
lemma pullback_map_globalScalar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : Γ(Y, ⊤)) (M : Y.Modules) :
    (Scheme.Modules.pullback f).map ((globalScalar Y r).app M) =
      (globalScalar X (f.appTop r)).app ((Scheme.Modules.pullback f).obj M) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  change (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
    (Scheme.Modules.pullback f ⋙ Scheme.Modules.pushforward f).map
      ((globalScalar Y r).app M) = _
  rw [← (Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality]
  rw [← globalScalar_pushforward]
  exact ((globalScalar Y r).naturality _).symm

end Quillen.SchemeSheaf
