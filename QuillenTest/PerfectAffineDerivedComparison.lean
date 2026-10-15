/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.DerivedComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.Homology

/-! # Consumers of actual affine derived comparison and perfect homology -/
@[expose] public section

open Quillen.PerfectComplexes


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes.Affine

namespace QuillenTest.PerfectAffineDerivedComparison

open Quillen

local instance standardDerivedModules (R : Type u) [Ring R] :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} R) := HasDerivedCategory.standard _

local instance standardDerivedSheaves (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- An arbitrary affine locally perfect complex, with no assumption on its
terms, has actual quasicoherent cohomology and a uniform finite amplitude. -/
theorem affinePerfect_homology (R : CommRingCat.{u}) (K : Perfect (Spec R)) :
    (∀ i : ℤ, (K.obj.homology i).IsQuasicoherent) ∧
      ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i → IsZero (K.obj.homology i) :=
  ⟨locallyPerfect_quasicoherent_homology K.property,
    locallyPerfect_homology_bounded K.property⟩

/-- The homology comparison uses the unchanged perfect restriction functor. -/
def principalPerfect_homology (R : CommRingCat.{u}) (r : R)
    (K : Perfect (Spec R)) (i : ℤ) :
    ((perfectRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj
      K).obj.homology i ≅
      (Scheme.Modules.restrictFunctor (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen
        R r)).obj (K.obj.homology i) :=
  restrictHomologyIso _ K.obj i

/-- The principal derived comparison commutes with arbitrary derived maps,
not just the images of chosen chain maps. -/
theorem principalDerived_comparison_natural (R : CommRingCat.{u}) (r : R)
    {K L : DerivedCategory (ModuleCat.{u} R)} (f : K ⟶ L) :
    (associatedDerived (CommRingCat.of (Localization.Away r))).map
        ((principalDerivedLocalization R r).map f) ≫
      (principalDerivedComparisonIso R r).hom.app L =
    (principalDerivedComparisonIso R r).hom.app K ≫
      (derivedRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).map
        ((associatedDerived R).map f) :=
  (principalDerivedComparisonIso R r).hom.naturality f

/-- Conservativity is available directly on arbitrary derived objects. -/
theorem associatedDerived_detects_isomorphism (R : CommRingCat.{u})
    {K L : DerivedCategory (ModuleCat.{u} R)} (f : K ⟶ L)
    [IsIso ((associatedDerived R).map f)] : IsIso f :=
  isIso_of_reflects_iso f (associatedDerived R)

/-- The affine comparison lands in the actual QC-cohomology part of the
ambient derived category of all sheaves. -/
theorem associatedDerived_has_quasicoherent_homology (R : CommRingCat.{u})
    (K : DerivedCategory (ModuleCat.{u} R)) (i : ℤ) :
    ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj
      ((associatedDerived R).obj K)).IsQuasicoherent :=
  associatedDerived_quasicoherent_homology R K i

end QuillenTest.PerfectAffineDerivedComparison
