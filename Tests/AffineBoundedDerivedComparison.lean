/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedDerivedComparison
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers of the bounded affine derived equivalence

The tests retain the original morphism map, exact requested chain bounds,
original localization and principal restriction, with zero-ring and
zero-divisor consumers. Original sheaf-complex terms need not be QC.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
namespace Quillen.Tests.AffineBoundedDerivedComparison
attribute [local instance] Quillen.PerfectComplexes.Affine.standardDerivedModules
  Quillen.PerfectComplexes.Affine.standardDerivedSheaves

lemma original_map_unique_lift (R : CommRingCat.{u})
    (K L : DerivedCategory (ModuleCat.{u} R)) (a b c d : ℤ)
    [K.IsGE a] [K.IsLE b] [L.IsGE c] [L.IsLE d]
    (f : (associatedDerived R).obj K ⟶ (associatedDerived R).obj L) :
    ∃! g : K ⟶ L, (associatedDerived R).map g = f :=
  (associatedDerived_bounded_map_bijective R K L a b c d).existsUnique f

lemma original_map_lifts_composition (R : CommRingCat.{u})
    (K L M : DerivedCategory.Bounded (ModuleCat.{u} R))
    (f : (associatedDerived R).obj K.obj ⟶ (associatedDerived R).obj L.obj)
    (g : (associatedDerived R).obj L.obj ⟶ (associatedDerived R).obj M.obj) :
    ∃ (a : K.obj ⟶ L.obj) (b : L.obj ⟶ M.obj),
      (associatedDerived R).map a = f ∧ (associatedDerived R).map b = g ∧
      (associatedDerived R).map (a ≫ b) = f ≫ g := by
  obtain ⟨a, ha⟩ := (associatedBoundedDerived R).map_surjective f
  obtain ⟨b, hb⟩ := (associatedBoundedDerived R).map_surjective g
  exact ⟨a.hom, b.hom, ha, hb, by rw [Functor.map_comp]; exact congrArg₂ (· ≫ ·) ha hb⟩

lemma equivalence_keeps_original_map (R : CommRingCat.{u})
    {K L : DerivedCategory.Bounded (ModuleCat.{u} R)} (f : K ⟶ L) :
    ((boundedDerivedEquivalence R).functor.map f).hom = (associatedDerived R).map f.hom := rfl

lemma equivalence_keeps_principal_restriction (R : CommRingCat.{u}) (r : R)
    (K : DerivedCategory.Bounded (ModuleCat.{u} R)) :
    Nonempty ((associatedDerived (CommRingCat.of (Localization.Away r))).obj
      ((principalDerivedLocalization R r).obj K.obj) ≅
      (derivedRestrict (CoherentScheme.principalOpen R r)).obj
        (((boundedDerivedEquivalence R).functor.obj K).obj)) :=
  ⟨(principalDerivedComparisonIso R r).app K.obj⟩


lemma forward_preserves_distinguished_triangles (R : CommRingCat.{u})
    (T : CategoryTheory.Pretriangulated.Triangle (DerivedCategory.Bounded (ModuleCat.{u} R)))
    (hT : T ∈ distTriang _) :
    (associatedBoundedQuasicoherent R).mapTriangle.obj T ∈
      distTriang (BoundedQuasicoherentDerived R) :=
  (associatedBoundedQuasicoherent R).map_distinguished T hT

lemma exact_requested_term_bounds (R : CommRingCat.{u}) (K : Derived (Spec R)) (a b : ℤ)
    [DerivedCategory.IsGE (C := (Spec R).Modules) K a]
    [DerivedCategory.IsLE (C := (Spec R).Modules) K b]
    (hK : ∀ i, ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj K).IsQuasicoherent) :
    ∃ (L : ModuleComplex R), L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧
      Nonempty ((toDerived (Spec R)).obj ((associatedComplex R).obj L) ≅ K) :=
  exists_bounded_module_representative_of_quasicoherent_homology R K a b hK

lemma empty_affine_exact_bounds
    (K : Derived (Spec (CommRingCat.of (ZMod 1)))) (a b : ℤ)
    [DerivedCategory.IsGE (C := (Spec (CommRingCat.of (ZMod 1))).Modules) K a]
    [DerivedCategory.IsLE (C := (Spec (CommRingCat.of (ZMod 1))).Modules) K b]
    (hK : ∀ i, ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of (ZMod 1))).Modules i).obj
      K).IsQuasicoherent) :
    ∃ (L : ModuleComplex (CommRingCat.of (ZMod 1))), L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧
      Nonempty ((toDerived _).obj ((associatedComplex _).obj L) ≅ K) :=
  exact_requested_term_bounds _ K a b hK

lemma zero_divisor_ring_essential_image
    (K : Derived (Spec (CommRingCat.of (ZMod 6)))) (a b : ℤ)
    [DerivedCategory.IsGE (C := (Spec (CommRingCat.of (ZMod 6))).Modules) K a]
    [DerivedCategory.IsLE (C := (Spec (CommRingCat.of (ZMod 6))).Modules) K b]
    (hK : ∀ i, ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of (ZMod 6))).Modules i).obj
      K).IsQuasicoherent) :
    (associatedBoundedDerived (CommRingCat.of (ZMod 6))).essImage K :=
  associatedBoundedDerived_essImage_of_quasicoherent_homology _ K a b hK

lemma locally_perfect_unrestricted_terms (R : CommRingCat.{u})
    (K : Complex (Spec R)) (hK : locallyPerfect (Spec R) K) :
    ∃ (L : ModuleComplex R) (a b : ℤ), L.IsStrictlyGE a ∧ L.IsStrictlyLE b ∧
      Nonempty ((toDerived (Spec R)).obj ((associatedComplex R).obj L) ≅
        (toDerived (Spec R)).obj K) :=
  locallyPerfect_exists_bounded_module_representative R hK

lemma exact_functor_reflects_both_bounds (R : CommRingCat.{u})
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) :
    (DerivedCategory.IsGE (C := (Spec R).Modules) ((associatedDerived R).obj K) a ∧
      DerivedCategory.IsLE (C := (Spec R).Modules) ((associatedDerived R).obj K) b) ↔
    K.IsGE a ∧ K.IsLE b := by
  rw [DerivedHomComparison.mapDerivedCategory_isGE_iff (tilde.functor R),
    DerivedHomComparison.mapDerivedCategory_isLE_iff (tilde.functor R)]

end Quillen.Tests.AffineBoundedDerivedComparison
