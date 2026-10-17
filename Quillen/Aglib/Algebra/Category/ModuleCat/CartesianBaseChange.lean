/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.BaseChange
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # The original scalar base-change mate

For a commuting algebra square, the extension/restriction-of-scalars mate retains the
original adjunction units. For a ring pushout it equals the canonical tensor cancellation
isomorphism, including the full pure-tensor formula. No flatness assumption is needed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory
namespace ModuleCat
variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B]
/-- The original restriction-of-scalars square comparison, with identity underlying maps. -/
def scalarSquareIso :
    restrictScalars (algebraMap A B) ⋙ restrictScalars (algebraMap R A) ≅
      restrictScalars (algebraMap S B) ⋙ restrictScalars (algebraMap R S) :=
  (restrictScalarsComp' (algebraMap R A) (algebraMap A B) (algebraMap R B)
    (IsScalarTower.algebraMap_eq R A B)).symm ≪≫
  restrictScalarsComp' (algebraMap R S) (algebraMap S B) (algebraMap R B)
    (IsScalarTower.algebraMap_eq R S B)
/-- The actual extension/restriction-of-scalars base-change mate. -/
def scalarBaseChangeNatTrans :
    restrictScalars (algebraMap R A) ⋙ extendScalars (algebraMap R S) ⟶
      extendScalars (algebraMap A B) ⋙ restrictScalars (algebraMap S B) :=
  ((mateEquiv (extendRestrictScalarsAdj (algebraMap A B))
    (extendRestrictScalarsAdj (algebraMap R S))).symm
      (TwoSquare.mk _ _ _ _ (scalarSquareIso R S A B).hom)).natTrans
/-- The base-change mate preserves the original extension-of-scalars units. -/
theorem scalarBaseChangeNatTrans_unit (M : ModuleCat A) :
    (restrictScalars (algebraMap R A)).map
        ((extendRestrictScalarsAdj (algebraMap A B)).unit.app M) ≫
      (scalarSquareIso R S A B).hom.app ((extendScalars (algebraMap A B)).obj M) =
    (extendRestrictScalarsAdj (algebraMap R S)).unit.app
        ((restrictScalars (algebraMap R A)).obj M) ≫
      (restrictScalars (algebraMap R S)).map ((scalarBaseChangeNatTrans R S A B).app M) :=
  unit_mateEquiv_symm (extendRestrictScalarsAdj (algebraMap A B))
    (extendRestrictScalarsAdj (algebraMap R S))
      (TwoSquare.mk _ _ _ _ (scalarSquareIso R S A B).hom) M
/-- On original unit generators the base-change mate is the original other unit generator. -/
theorem scalarBaseChangeMap_unit_apply (M : ModuleCat A) (m : M) :
    (scalarBaseChangeNatTrans R S A B).app M
        (((extendRestrictScalarsAdj (algebraMap R S)).unit.app
          ((restrictScalars (algebraMap R A)).obj M)) m) =
      ((extendRestrictScalarsAdj (algebraMap A B)).unit.app M) m := by
  have h := congrArg (fun q => q m) (scalarBaseChangeNatTrans_unit R S A B M)
  simpa [scalarSquareIso] using h.symm
/-- The canonical tensor cancellation isomorphism on an actual module object. -/
def scalarBaseChangeIsoApp [Algebra.IsPushout R S A B] (M : ModuleCat A) :
    (restrictScalars (algebraMap R A) ⋙ extendScalars (algebraMap R S)).obj M ≅
      (extendScalars (algebraMap A B) ⋙ restrictScalars (algebraMap S B)).obj M := by
  have htA := (inferInstance : IsScalarTower R A B)
  have htS := (inferInstance : IsScalarTower R S B)
  have hp := (inferInstance : Algebra.IsPushout R S A B)
  have ers := @toAlgebra_algebraMap R S _ _ ‹Algebra R S›
  have eab := @toAlgebra_algebraMap A B _ _ ‹Algebra A B›
  have esb := @toAlgebra_algebraMap S B _ _ ‹Algebra S B›
  letI rs : Algebra R S := (algebraMap R S).toAlgebra
  letI ab : Algebra A B := (algebraMap A B).toAlgebra
  letI sb : Algebra S B := (algebraMap S B).toAlgebra
  letI : IsScalarTower R A B := by simpa +instances only [ab, eab] using htA
  letI : IsScalarTower R S B := by simpa +instances only [rs, sb, ers, esb] using htS
  letI : Algebra.IsPushout R S A B := by
    convert hp using 1
  letI : Module R M := Module.compHom M (algebraMap R A)
  letI : IsScalarTower R A M := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact (Algebra.IsPushout.cancelBaseChange R S A B M).symm.toModuleIso

variable [Algebra.IsPushout R S A B]

/-- The canonical tensor cancellation sends the original unit generator to the other unit. -/
theorem scalarBaseChangeIsoApp_unit_apply (M : ModuleCat A) (m : M) :
    (scalarBaseChangeIsoApp R S A B M).hom
        (((extendRestrictScalarsAdj (algebraMap R S)).unit.app
          ((restrictScalars (algebraMap R A)).obj M)) m) =
      ((extendRestrictScalarsAdj (algebraMap A B)).unit.app M) m := by
  simp only [scalarBaseChangeIsoApp, LinearEquiv.toModuleIso_hom, hom_ofHom]
  erw [extendRestrictScalarsAdj_unit_app_apply, extendRestrictScalarsAdj_unit_app_apply]
  erw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
  simp
/-- The original base-change mate is the canonical tensor cancellation map. -/
theorem scalarBaseChangeMap_eq_isoApp (M : ModuleCat A) :
    (scalarBaseChangeNatTrans R S A B).app M = (scalarBaseChangeIsoApp R S A B M).hom := by
  apply ((extendRestrictScalarsAdj (algebraMap R S)).homEquiv _ _).injective
  apply ModuleCat.hom_ext
  ext m
  change (scalarBaseChangeNatTrans R S A B).app M
      (((extendRestrictScalarsAdj (algebraMap R S)).unit.app
        ((restrictScalars (algebraMap R A)).obj M)) m) =
    (scalarBaseChangeIsoApp R S A B M).hom
      (((extendRestrictScalarsAdj (algebraMap R S)).unit.app
        ((restrictScalars (algebraMap R A)).obj M)) m)
  rw [scalarBaseChangeMap_unit_apply, scalarBaseChangeIsoApp_unit_apply]
open scoped TensorProduct ChangeOfRings in
/-- On every pure tensor the original mate is the canonical scalar extension map. -/
theorem scalarBaseChangeMap_tmul (M : ModuleCat A) (s : S) (m : M) :
    (scalarBaseChangeNatTrans R S A B).app M (s ⊗ₜ[R, algebraMap R S] m) =
      algebraMap S B s ⊗ₜ[A, algebraMap A B] m := by
  rw [scalarBaseChangeMap_eq_isoApp]
  simp only [scalarBaseChangeIsoApp, LinearEquiv.toModuleIso_hom, hom_ofHom]
  erw [Algebra.IsPushout.cancelBaseChange_symm_tmul]
  rfl
/-- The original scalar base-change mate is invertible for a genuine ring pushout. -/
theorem scalarBaseChangeMap_isIso : IsIso (scalarBaseChangeNatTrans R S A B) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [scalarBaseChangeMap_eq_isoApp]
  infer_instance
end ModuleCat
