/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Basic
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Locality
public import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Unit module properties and actual open-immersion global-section maps -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.ProjectiveLine
lemma gammaIsoTop_inv {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (IsOpenImmersion.ΓIsoTop f).inv = f.appLE f.opensRange ⊤ (by simp) := by
  simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, eqToIso.inv, eqToHom_op, Iso.symm_inv,
    Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

theorem isQuasicoherent_unit (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent := by
  let e : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} Unit) ≅
      SheafOfModules.unit X.ringCatSheaf := coproductUniqueIso _
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e (by infer_instance)

lemma restrict_gammaIsoTop_inv {W Y X : Scheme.{u}} (g : W ⟶ Y) (f : Y ⟶ X)
    [IsOpenImmersion g] [IsOpenImmersion f]
    (hle : (g ≫ f).opensRange ≤ f.opensRange) :
    X.presheaf.map (homOfLE hle).op ≫ (IsOpenImmersion.ΓIsoTop (g ≫ f)).inv =
      (IsOpenImmersion.ΓIsoTop f).inv ≫ g.appTop := by
  rw [gammaIsoTop_inv, gammaIsoTop_inv, Scheme.Hom.map_appLE]
  rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  rfl


theorem finiteLocallyFree_unit (X : Scheme.{u}) :
    IsFiniteLocallyFree X (SheafOfModules.unit X.ringCatSheaf) := by
  let e : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} Unit) ≅
      SheafOfModules.unit X.ringCatSheaf := coproductUniqueIso _
  exact finiteLocallyFree_of_iso e

end AlgebraicGeometry.Scheme.ProjectiveLine
