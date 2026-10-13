/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.UnitSections

/-!
# Scalar multiplication on actual module sheaves

Global ring sections act naturally on every module sheaf. The action commutes with original open
restriction and specializes to the structure-module action.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Quillen.SchemeSheaf
variable {X : Scheme.{u}}

/-- Multiplication by an original global ring section on a module sheaf. -/
def moduleMul (M : X.Modules) (s : Γ(X, ⊤)) : M ⟶ M where
  val :=
    { app := fun U => by
        letI : CommRing (X.ringCatSheaf.obj.obj U) :=
          inferInstanceAs (CommRing (Γ(X, U.unop)))
        let a : X.ringCatSheaf.obj.obj U :=
          (X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom s
        exact ModuleCat.ofHom
          { toFun := fun x => a • x
            map_add' := fun x y => smul_add _ x y
            map_smul' := fun r x => smul_comm a r x }
      naturality := by
        intro U V f
        ext x
        change (X.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op).hom s •
            (M.val.map f) x = (M.val.map f)
              ((X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom s • x)
        rw [M.val.map_smul]
        congr 1
        change (X.presheaf.map (homOfLE (show V.unop ≤ ⊤ from le_top)).op).hom s =
          (X.presheaf.map f).hom
            ((X.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom s)
        rw [← CommRingCat.comp_apply, ← Functor.map_comp]
        rfl }

lemma moduleMul_app (M : X.Modules) (s : Γ(X, ⊤)) (U : X.Opens) (m : Γ(M, U)) :
    (Scheme.Modules.Hom.app (moduleMul M s) U).hom m =
      (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom s • m := rfl

lemma moduleMul_naturality {M N : X.Modules} (f : M ⟶ N) (s : Γ(X, ⊤)) :
    moduleMul M s ≫ f = f ≫ moduleMul N s := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  exact Scheme.Modules.Hom.app_smul f _ x

lemma moduleMul_one (M : X.Modules) : moduleMul M 1 = 𝟙 M := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  simp [moduleMul_app]

lemma moduleMul_mul (M : X.Modules) (s t : Γ(X, ⊤)) :
    moduleMul M (s * t) = moduleMul M s ≫ moduleMul M t := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  simp [moduleMul_app, mul_smul]

lemma moduleMul_restrict {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (M : X.Modules) (s : Γ(X, ⊤)) :
    (Scheme.Modules.restrictFunctor j).map (moduleMul M s) =
      moduleMul (M.restrict j) (j.appTop.hom s) := by
  apply Scheme.Modules.hom_ext
  intro V
  ext x
  change Γ(M, j ''ᵁ V) at x
  change (X.presheaf.map (homOfLE (show j ''ᵁ V ≤ ⊤ from le_top)).op).hom s • x =
    (j.appIso V).inv.hom
      ((U.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op).hom (j.appTop.hom s)) • x
  congr 1
  apply (ConcreteCategory.bijective_of_isIso (j.appIso V).hom).1
  have h : X.presheaf.map (homOfLE (show j ''ᵁ V ≤ ⊤ from le_top)).op ≫
      (j.appIso V).hom = j.appTop ≫ U.presheaf.map (homOfLE le_top).op := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE, Scheme.Hom.appTop,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  simpa only [← CommRingCat.comp_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    congrArg (fun f => CommRingCat.Hom.hom f s) h

/-- Multiplication by a global unit as an automorphism of the original module sheaf. -/
def moduleMulIso (M : X.Modules) (s : (Γ(X, ⊤))ˣ) : M ≅ M where
  hom := moduleMul M s
  inv := moduleMul M (↑s⁻¹)
  hom_inv_id := by rw [← moduleMul_mul]; simpa using moduleMul_one M
  inv_hom_id := by rw [← moduleMul_mul]; simpa using moduleMul_one M

lemma moduleMul_unit (s : Γ(X, ⊤)) :
    moduleMul (SheafOfModules.unit X.ringCatSheaf) s = unitMul X s := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change Γ(X, U) at x
  change (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom s * x =
    x * (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom s
  exact mul_comm _ _

end Quillen.SchemeSheaf
