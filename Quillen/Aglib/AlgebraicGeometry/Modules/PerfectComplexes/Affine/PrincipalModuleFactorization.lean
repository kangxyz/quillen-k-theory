/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.Algebra.Homology.CochainComplex.HomotopySquareStrictification
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.DerivedModuleReplacement
public import Aglib.Algebra.Homology.DerivedCategory.KProjective.Comparison

/-!
# Genuine principal map factorization in bounded-projective module models

Actual K-projectivity lifts a map through a witnessed localized
quasi-isomorphism up to homotopy. A proved finite denominator descends that
lift; the scalar becomes an actual chain automorphism after localization.
The genuine identity-cone cylinder then supplies an exact commuting triangle
with bounded finite-projective original-ring middle object. The target module
complex is unrestricted apart from its actual localized strict witness.
-/
@[expose] public section

open Quillen.CochainComplex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes.Affine

/-- The actual identity-cone cylinder retains bounded finite projectivity. -/
theorem moduleStrictPerfect_mapCylinder (R : CommRingCat.{u})
    {A E : ModuleComplex R} (hA : moduleStrictPerfect R A) (hE : moduleStrictPerfect R E) :
    moduleStrictPerfect R (mapCylinder A E) := by
  obtain ⟨⟨a, b, hbA⟩, hpA⟩ := hA
  obtain ⟨⟨c, d, hbE⟩, hpE⟩ := hE
  let e (i : ℤ) : (mapCylinder A E).X i ≅
      ModuleCat.of R (E.X i × (A.X (i + 1) × A.X i)) :=
    (HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) i).mapBiprod _ _ ≪≫
      biprod.mapIso (Iso.refl _) (homotopyCofiber.XIsoBiprod (𝟙 A) i (i+1) rfl ≪≫
        ModuleCat.biprodIsoProd _ _) ≪≫ ModuleCat.biprodIsoProd _ _
  refine ⟨⟨min (a - 1) c, max b d, fun i hi => ?_⟩, fun i => ?_⟩
  · let := ModuleCat.isZero_iff_subsingleton.mp (hbE i (by omega))
    let := ModuleCat.isZero_iff_subsingleton.mp (hbA i (by omega))
    let := ModuleCat.isZero_iff_subsingleton.mp (hbA (i+1) (by omega))
    exact (ModuleCat.isZero_of_subsingleton _).of_iso (e i)
  · let := (hpE i).1
    let := (hpE i).2
    let := (hpA i).1
    let := (hpA i).2
    let := (hpA (i+1)).1
    let := (hpA (i+1)).2
    exact ⟨Module.Finite.equiv (e i).toLinearEquiv.symm,
      Module.Projective.of_equiv (e i).toLinearEquiv.symm⟩

/-- A target with an actual localized strict witness admits a genuine
strictly commuting principal-open map factorization for a strict source. -/
theorem exists_principal_module_map_factorization (R : CommRingCat.{u}) (r : R)
    {A E : ModuleComplex R} (hA : moduleStrictPerfect R A) (hE : moduleStrictPerfect R E)
    {B : ModuleComplex (.of (Localization.Away r))}
    (q : (localize r (.up ℤ)).obj E ⟶ B) [QuasiIso q]
    (f : (localize r (.up ℤ)).obj A ⟶ B) :
    ∃ (M : ModuleComplex R) (a : A ⟶ M)
      (p : (localize r (.up ℤ)).obj M ⟶ B),
      moduleStrictPerfect R M ∧ QuasiIso p ∧ (localize r (.up ℤ)).map a ≫ p = f := by
  let F := localize r (.up ℤ)
  have : CochainComplex.IsKProjective (F.obj A) :=
    isKProjective_of_moduleStrictPerfect _ (moduleStrictPerfect_localize R r hA)
  obtain ⟨g, ⟨H⟩⟩ := _root_.CochainComplex.exists_lift_quasiIso_up_to_homotopy q f
  obtain ⟨n, a, _, ha⟩ := exists_moduleStrictPerfect_fraction R r hA g
  let d : E ⟶ E := r ^ n • 𝟙 E
  have hd : IsIso (F.map d) := localize_power_id_isIso r E n
  let q' : F.obj E ⟶ B := inv (F.map d) ≫ q
  have hga : F.map a = g ≫ F.map d := by
    rw [← ha]
    simp only [d, F, localize_map_smul, CategoryTheory.Functor.map_id,
      Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  have Heq : F.map a ≫ q' = g ≫ q := by simp [q', hga]
  have H' : Homotopy (F.map a ≫ q') f := Heq.symm ▸ H
  obtain ⟨p, hp, hcomm, _⟩ := exists_mapCylinder_strictification
    (ModuleCat.localizedModuleFunctor (Submonoid.powers r)) a q' f H'
  exact ⟨mapCylinder A E, mapCylinderInclusion a, p,
    moduleStrictPerfect_mapCylinder R hA hE, hp, hcomm⟩

end Quillen.PerfectComplexes.Affine
