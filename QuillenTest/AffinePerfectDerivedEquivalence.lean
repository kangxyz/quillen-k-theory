/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PerfectDerivedEquivalence
public import Mathlib.Data.ZMod.Basic
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Restriction
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.DerivedPerfect
/-!
# Original-map consumers of affine perfect derived comparison

These consumers retain actual Hom maps, original geometric restriction and
scalar localization, exact cohomological bounds, genuine distinguished
triangles, and the empty affine scheme. Detection of perfectness does not
require a supplied bound; detection of weak chain maps uses original
quasi-isomorphisms.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules (derivedRestrict)

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.PerfectComplexes


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Quillen.PerfectComplexes.Affine
attribute [local instance] Quillen.PerfectComplexes.Affine.standardDerivedModules
  Quillen.PerfectComplexes.Affine.standardDerivedSheaves
namespace QuillenTest.AffinePerfectDerivedEquivalence

open Quillen

lemma unique_original_map_lift (R : CommRingCat.{u}) (K L : PerfectModuleDerived R)
    (f : (associatedDerived R).obj K.obj ⟶ (associatedDerived R).obj L.obj) :
    ∃! g : K ⟶ L, (associatedDerived R).map g.hom = f := by
  obtain ⟨g, hg⟩ := (associatedPerfectDerived R).map_surjective f
  exact ⟨g, hg, fun g' hg' => (associatedPerfectDerived R).map_injective (hg'.trans hg.symm)⟩

lemma literal_equivalence_forward_map (R : CommRingCat.{u})
    {K L : PerfectModuleDerived R} (f : K ⟶ L) :
    ((perfectDerivedEquivalence R).functor.map f).hom = (associatedDerived R).map f.hom := rfl

lemma original_perfect_restriction_map {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    {K L : Perfect X} (f : K ⟶ L) :
    (derivedRestrict j).map ((DerivedCategory.Q (C := X.Modules)).map f.hom) ≫
      ((Scheme.Modules.perfectDerivedRestrictFactors j).hom.app L).hom =
    ((Scheme.Modules.perfectDerivedRestrictFactors j).hom.app K).hom ≫
      (DerivedCategory.Q (C := U.Modules)).map (((perfectRestrict j).map f).hom) := by
  exact congrArg (fun g => g.hom) ((Scheme.Modules.perfectDerivedRestrictFactors
    j).hom.naturality f)

lemma original_principal_comparison_naturality (R : CommRingCat.{u}) (r : R)
    {K L : PerfectModuleDerived R} (f : K ⟶ L) :
    (associatedDerived (CommRingCat.of (Localization.Away r))).map
      ((principalDerivedLocalization R r).map f.hom) ≫
      ((perfectDerivedEquivalencePrincipalIso R r).hom.app L).hom =
    ((perfectDerivedEquivalencePrincipalIso R r).hom.app K).hom ≫
      (derivedRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map
        ((associatedDerived R).map f.hom) := by
  exact congrArg (fun g => g.hom) ((perfectDerivedEquivalencePrincipalIso R r).hom.naturality f)

lemma exact_bounds_of_inverse_model (R : CommRingCat.{u}) (K : Scheme.Modules.PerfectDerived
  (Spec R))
    (a b : ℤ)
    [DerivedCategory.IsGE (C := (Spec R).Modules) K.obj a]
    [DerivedCategory.IsLE (C := (Spec R).Modules) K.obj b] :
    ∃ A : PerfectModuleDerived R, A.obj.IsGE a ∧ A.obj.IsLE b ∧
      Nonempty ((associatedDerived R).obj A.obj ≅ K.obj) := by
  let A := (associatedPerfect R).objPreimage K
  let e := (associatedPerfect R).objObjPreimageIso K
  let e' : (associatedDerived R).obj A.obj ≅ K.obj :=
    (Scheme.Modules.perfectDerivedObjects (Spec R)).ι.mapIso e
  have hge := (DerivedCategory.TStructure.t (C := (Spec R).Modules)).isGE_of_iso e'.symm a
  have hle := (DerivedCategory.TStructure.t (C := (Spec R).Modules)).isLE_of_iso e'.symm b
  exact ⟨A, (perfectDerivedEquivalence_isGE_iff R A a).mp hge,
    (perfectDerivedEquivalence_isLE_iff R A b).mp hle, ⟨e'⟩⟩

lemma actual_distinguished_triangle_image (R : CommRingCat.{u})
    (T : Triangle (PerfectModuleDerived R)) (hT : T ∈ distTriang _) :
    (associatedPerfect R).mapTriangle.obj T ∈ distTriang (Scheme.Modules.PerfectDerived (Spec R)) :=
  (associatedPerfect R).map_distinguished T hT

lemma empty_affine_every_derived_object
    (K : DerivedCategory (Spec (CommRingCat.of (ZMod 1))).Modules) :
    ∃ P : PerfectModuleDerived (CommRingCat.of (ZMod 1)),
      Nonempty ((associatedDerived (CommRingCat.of (ZMod 1))).obj P.obj ≅ K) := by
  have hK : Scheme.Modules.perfectDerivedObjects (Spec (CommRingCat.of (ZMod 1))) K := by
    intro x
    change PrimeSpectrum (ZMod 1) at x
    exact False.elim (x.isPrime.ne_top (Subsingleton.elim _ _))
  exact (associatedPerfectDerived_essImage_iff _ K).mpr hK

lemma perfect_reflection_without_bound_input (R : CommRingCat.{u})
    (K : DerivedCategory (ModuleCat.{u} R))
    (hK : Scheme.Modules.perfectDerivedObjects (Spec R) ((associatedDerived R).obj K)) :
    ∃ P : ModuleComplex R, moduleStrictPerfect R P ∧ Nonempty (DerivedCategory.Q.obj P ≅ K) :=
  (finiteProjectiveDerived_iff_associated_perfect R K).mpr hK

lemma original_weak_map_detection {X : Scheme.{u}} {K L : Perfect X} (f : K ⟶ L) :
    IsIso ((Scheme.Modules.perfectToDerived X).map f) ↔ QuasiIso f.hom :=
  Scheme.Modules.perfectToDerived_isIso_map_iff f

end QuillenTest.AffinePerfectDerivedEquivalence
