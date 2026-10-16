/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction
public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Tensor.Exact

/-!
# Actual tensor unit sections and specified multiplication trivializations

Two specified unit charts give the original tensor multiplication isomorphism.
The actual section formula is multiplication of the original unit-coordinate
sections, retaining the native sheafified tensor and unitor maps.
-/

@[expose] public section
open Quillen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
  SheafOfModulesOfCommRing
open CategoryTheory.MonoidalCategory
attribute [local instance] Abelian.hasFiniteBiproducts
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open AlgebraicGeometry.Scheme.Modules

/-- The original left unitor sends each original pure-tensor generator to scalar multiplication. -/
lemma tensorLeftUnit_section (X : Scheme.{u}) (M : X.Modules) (U : X.Opens)
    (r : Γ(X, U)) (m : Γ(M, U)) :
    ((tensorLeftUnitIso X.sheaf).hom.app M).val.app (op U)
        (moduleTensorSection X (SheafOfModules.unit X.ringCatSheaf) M U r m) = r • m := by
  exact congrArg (fun f => f.app (op U) (r ⊗ₜ[Γ(X, U)] m))
    (associatedSheafUnit_tensorLeftUnitIso X.sheaf M)

/-- Two specified unit trivializations give the original tensor multiplication chart isomorphism. -/
def tensorPairingTrivialization {X Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j]
    (M N : X.Modules) (eM : M.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (eN : N.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf) :
    ((moduleTensorLeftFunctor X M).obj N).restrict j ≅ SheafOfModules.unit Y.ringCatSheaf :=
  (tensorRestrictionIso j M N).symm ≪≫
    ((tensorFunctor Y.sheaf).mapIso eM).app (N.restrict j) ≪≫
    (tensorLeftUnitIso Y.sheaf).app (N.restrict j) ≪≫ eN

lemma tensorPairingTrivialization_section {X Y : Scheme.{u}}
    (j : Y ⟶ X) [IsOpenImmersion j] (M N : X.Modules)
    (eM : M.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (eN : N.restrict j ≅ SheafOfModules.unit Y.ringCatSheaf)
    (U : Y.Opens) (m : Γ(M.restrict j, U)) (n : Γ(N.restrict j, U)) :
    ((tensorRestrictionIso j M N).hom ≫
      (tensorPairingTrivialization j M N eM eN).hom).val.app (op U)
        (moduleTensorSection Y (M.restrict j) (N.restrict j) U m n) =
      (show Γ(Y, U) from eM.hom.val.app (op U) m) *
        (show Γ(Y, U) from eN.hom.val.app (op U) n) := by
  have h : (tensorRestrictionIso j M N).hom ≫
      (tensorPairingTrivialization j M N eM eN).hom =
        (moduleTensorCoefficientMap Y eM.hom).app (N.restrict j) ≫
          (tensorLeftUnitIso Y.sheaf).hom.app (N.restrict j) ≫ eN.hom := by
    simp only [tensorPairingTrivialization, Iso.trans_hom, Iso.symm_hom,
      Iso.hom_inv_id_assoc, Iso.app_hom, Functor.mapIso_hom]
    rfl
  rw [h]
  change eN.hom.val.app (op U)
    (((tensorLeftUnitIso Y.sheaf).hom.app (N.restrict j)).val.app (op U)
      (((moduleTensorCoefficientMap Y eM.hom).app (N.restrict j)).app U
        (moduleTensorSection Y (M.restrict j) (N.restrict j) U m n))) = _
  rw [moduleTensorCoefficientMap_section eM.hom (N.restrict j) U m n]
  erw [tensorLeftUnit_section Y (N.restrict j) U (eM.hom.val.app (op U) m) n]
  rw [_root_.map_smul]
  rfl

end AlgebraicGeometry.Scheme.ProjectiveLine
