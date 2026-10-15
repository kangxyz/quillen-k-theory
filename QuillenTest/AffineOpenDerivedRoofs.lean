/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenDerivedRoofs
public import Mathlib.Data.ZMod.Basic

/-! Original-map consumers for geometric qc-open roofs and equality denominators. -/
@[expose] public section

open Quillen.PerfectComplexes


open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
universe u
attribute [local instance] Affine.standardDerivedModules Affine.standardDerivedSheaves
namespace QuillenTest.AffineOpenDerivedRoofs

open Quillen

variable (R : CommRingCat.{u})

lemma original_counit_factorization {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
    {P : ModuleComplex R} {I : Complex U}
    (q : (restrict j).obj ((associatedComplex R).obj P) ⟶ I) :
    (restrict j).map ((associatedComplex R).map (openModuleChainAdjoint R j q)) ≫
      ((restrict j).map (associatedSectionsCounit R ((pushforwardComplex j).obj I)) ≫
        (pushforwardComplexRestrictIso j).hom.app I) = q :=
  openModuleChainAdjoint_counit R j q

lemma original_transpose_homotopy {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
    {P : ModuleComplex R} {I : Complex U}
    {f g : (restrict j).obj ((associatedComplex R).obj P) ⟶ I} (H : Homotopy f g) :
    Nonempty (Homotopy (openModuleChainAdjoint R j f) (openModuleChainAdjoint R j g)) ∧
      DerivedCategory.Q.map (openModuleChainAdjoint R j f) =
        DerivedCategory.Q.map (openModuleChainAdjoint R j g) := by
  let H' := openModuleChainAdjointHomotopy R j H
  exact ⟨⟨H'⟩, DerivedCategory.Q_map_eq_of_homotopy _ H'⟩

lemma actual_chart_homology_maps (W : (Spec R).Opens) {P B : ModuleComplex R} (f : P ⟶ B)
    [QuasiIso ((restrict W.ι).map ((associatedComplex R).map f))]
    (r : R) (hr : PrimeSpectrum.basicOpen r ≤ W) (n : ℤ) :
    IsIso (homologyMap ((localize r (.up ℤ)).map f) n) := by
  have := quasiIso_localize_of_restrict_associated R W f r hr
  infer_instance

lemma empty_cover_original_weakness {P B : ModuleComplex R} (f : P ⟶ B) :
    QuasiIso ((restrict (⊥ : (Spec R).Opens).ι).map ((associatedComplex R).map f)) := by
  apply quasiIso_restrict_associated_of_principalUnion R ⊥ ∅ (by
    simp [Quillen.SheafCohomology.principalUnion]) f
  simp

lemma original_roof_inverse (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {P B : ModuleComplex R} (hP : moduleStrictPerfect R P) (hB : moduleStrictPerfect R B)
    (α : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)) ⟶
      (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj B))) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (t : P' ⟶ P) (g : P' ⟶ B)
      (_ : QuasiIso ((restrict W.ι).map ((associatedComplex R).map t))),
      α = inv ((toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t))) ≫
        (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)) := by
  obtain ⟨P', hP', t, g, ht, hsq⟩ := exists_quasiCompact_open_strict_module_roof R W hW hP hB α
  refine ⟨P', hP', t, g, ht, ?_⟩
  rw [← hsq, IsIso.inv_hom_id_assoc]

lemma original_iso_roof_both_weak (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    {P B : ModuleComplex R} (hP : moduleStrictPerfect R P) (hB : moduleStrictPerfect R B)
    (e : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)) ≅
      (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj B))) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (t : P' ⟶ P) (g : P' ⟶ B),
      QuasiIso ((restrict W.ι).map ((associatedComplex R).map t)) ∧
      QuasiIso ((restrict W.ι).map ((associatedComplex R).map g)) ∧
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t)) ≫ e.hom =
        (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)) := by
  obtain ⟨P', hP', t, g, ht, hsq⟩ :=
    exists_quasiCompact_open_strict_module_roof R W hW hP hB e.hom
  refine ⟨P', hP', t, g, ht, ?_, hsq⟩
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp
  change IsIso ((toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)))
  rw [← hsq]
  infer_instance

lemma lower_bounded_target_and_every_chart (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) {P B : ModuleComplex R}
    (hP : moduleStrictPerfect R P) (b : ℤ) [B.IsGE b]
    (α : (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj P)) ⟶
      (toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj B))) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (t : P' ⟶ P) (g : P' ⟶ B),
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map t)) ≫ α =
        (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g)) ∧
      ∀ r : R, PrimeSpectrum.basicOpen r ≤ W → ∀ n : ℤ,
        IsIso (homologyMap ((localize r (.up ℤ)).map t) n) := by
  obtain ⟨P', hP', t, g, ht, hsq⟩ :=
    exists_quasiCompact_open_derived_module_roof R W hW hP b α
  exact ⟨P', hP', t, g, hsq, fun r hr n => actual_chart_homology_maps R W t r hr n⟩

lemma global_equality_homotopy_and_localized_equations (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) {P B : ModuleComplex R}
    (hP : moduleStrictPerfect R P) (hB : moduleStrictPerfect R B) (f g : P ⟶ B)
    (hfg : (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map f)) =
      (toDerived W.toScheme).map ((restrict W.ι).map ((associatedComplex R).map g))) :
    ∃ (P' : ModuleComplex R) (_ : moduleStrictPerfect R P') (t : P' ⟶ P),
      QuasiIso ((restrict W.ι).map ((associatedComplex R).map t)) ∧
      Nonempty (Homotopy (t ≫ f) (t ≫ g)) ∧
      ∀ r : R, DerivedCategory.Q.map ((localize r (.up ℤ)).map (t ≫ f)) =
        DerivedCategory.Q.map ((localize r (.up ℤ)).map (t ≫ g)) := by
  obtain ⟨P', hP', t, ht, ⟨H⟩⟩ :=
    exists_quasiCompact_open_strict_module_equality R W hW hP hB f g hfg
  exact ⟨P', hP', t, ht, ⟨H⟩, fun r => DerivedCategory.Q_map_eq_of_homotopy _
    ((ModuleCat.localizedModuleFunctor (Submonoid.powers r)).mapHomotopy H)⟩

lemma zero_divisor_ring_empty_open
    {P B : ModuleComplex (CommRingCat.of (ZMod 6))}
    (hP : moduleStrictPerfect (CommRingCat.of (ZMod 6)) P)
    (hB : moduleStrictPerfect (CommRingCat.of (ZMod 6)) B)
    (α : (toDerived (⊥ : (Spec (CommRingCat.of (ZMod 6))).Opens).toScheme).obj
        ((restrict (⊥ : (Spec (CommRingCat.of (ZMod 6))).Opens).ι).obj
          ((associatedComplex (CommRingCat.of (ZMod 6))).obj P)) ⟶
      (toDerived (⊥ : (Spec (CommRingCat.of (ZMod 6))).Opens).toScheme).obj
        ((restrict (⊥ : (Spec (CommRingCat.of (ZMod 6))).Opens).ι).obj
          ((associatedComplex (CommRingCat.of (ZMod 6))).obj B))) :
    ∃ (P' : ModuleComplex (CommRingCat.of (ZMod 6)))
      (_ : moduleStrictPerfect (CommRingCat.of (ZMod 6)) P') (t : P' ⟶ P) (g : P' ⟶ B),
      (toDerived (⊥ : (Spec (CommRingCat.of (ZMod 6))).Opens).toScheme).map
        ((restrict (⊥ : (Spec (CommRingCat.of (ZMod 6))).Opens).ι).map
          ((associatedComplex (CommRingCat.of (ZMod 6))).map t)) ≫ α =
      (toDerived (⊥ : (Spec (CommRingCat.of (ZMod 6))).Opens).toScheme).map
        ((restrict (⊥ : (Spec (CommRingCat.of (ZMod 6))).Opens).ι).map
          ((associatedComplex (CommRingCat.of (ZMod 6))).map g)) := by
  obtain ⟨P', hP', t, g, _, hsq⟩ :=
    exists_quasiCompact_open_strict_module_roof (CommRingCat.of (ZMod 6)) ⊥
      (by simp)
      hP hB α
  exact ⟨P', hP', t, g, hsq⟩

end QuillenTest.AffineOpenDerivedRoofs
