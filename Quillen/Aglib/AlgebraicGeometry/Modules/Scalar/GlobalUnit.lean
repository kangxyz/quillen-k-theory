/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
Original global functions act on every actual module sheaf, and original units act by natural
automorphisms with their literal inverse scalar.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- Actual multiplication by a global function on every original module sheaf. -/
def globalScalar (X : Scheme.{u}) (r : Γ(X, ⊤)) : 𝟭 X.Modules ⟶ 𝟭 X.Modules where
  app M := { val := {
    app U := ModuleCat.ofHom {
      toFun m := X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r • m
      map_add' m n := smul_add _ m n
      map_smul' a m := by
        let : Module (X.presheaf.obj U) (M.val.obj U) :=
          inferInstanceAs (Module (X.ringCatSheaf.obj.obj U) (M.val.obj U))
        exact @smul_comm (X.presheaf.obj U) (X.presheaf.obj U) (M.val.obj U) _ _ inferInstance _ a m
          }
    naturality := by
      intro U V f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro m
      change X.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op r • M.val.map f m =
        M.val.map f (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op r • m)
      rw [M.val.map_smul]
      congr 1
      change X.presheaf.map _ r = (X.presheaf.map _ ≫ X.presheaf.map f) r
      rw [← Functor.map_comp]
      rfl } }
  naturality M N f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    exact ((f.val.app U).hom.map_smul _ m).symm

/--
A genuine global unit acts by an original natural automorphism, with the literal inverse scalar.
-/
def globalUnitIso (X : Scheme.{u}) (r : (Γ(X, ⊤))ˣ) : 𝟭 X.Modules ≅ 𝟭 X.Modules where
  hom := globalScalar X r
  inv := globalScalar X (↑r⁻¹)
  hom_inv_id := by
    apply NatTrans.ext
    funext M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (↑r⁻¹)) •
      ((X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (↑r)) • m) = m
    rw [smul_smul, ← map_mul, Units.inv_mul, map_one, one_smul]
  inv_hom_id := by
    apply NatTrans.ext
    funext M
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (↑r)) •
      ((X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op (↑r⁻¹)) • m) = m
    rw [smul_smul, ← map_mul, Units.mul_inv, map_one, one_smul]

end AlgebraicGeometry.Scheme.Modules
