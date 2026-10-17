/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.Algebra.Homology.ModuleCat.PrincipalFreeDescent
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Affine.StrictModuleModel

/-!
# Actual finite-free strict-complex extension from an affine principal open

The genuine bounded finite-free module descent theorem and the original
affine reconstruction/restriction isomorphisms extend strict-perfect targets
whose actual global-section terms are free. The result is an actual geometric
chain isomorphism, hence membership in the honest essential image of strict
restriction. Extension of arbitrary projective targets, stabilization and
full Thomason–Trobaugh cofinality remain separate.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization

/-- A strict complex on an affine principal open with genuinely finite-free
module terms extends to a strict complex on the original affine scheme,
with an actual geometric chain isomorphism after restriction. -/
theorem exists_principal_strict_extension_of_free_sections (R : CommRingCat.{u}) (r : R)
    (P : StrictPerfect (Spec (.of (Localization.Away r))))
    (hfree : ∀ i, Module.Free (Localization.Away r)
      (((sectionsComplex (.of (Localization.Away r))).obj P.obj).X i)) :
    ∃ Q : StrictPerfect (Spec R), Nonempty
      ((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj Q.obj ≅
        P.obj) := by
  let S := CommRingCat.of (Localization.Away r)
  let K := (sectionsComplex S).obj P.obj
  have hK := moduleStrictPerfect_sections S P.property
  obtain ⟨a, b, hb⟩ := hK.1
  obtain ⟨Q, hQbound, hQfree, ⟨eQ⟩⟩ :=
    exists_bounded_finiteFree_complex_descent r K a b hb hfree (fun i => (hK.2 i).1)
  have hQ : moduleStrictPerfect R Q := by
    refine ⟨⟨a, b, hQbound⟩, fun i => ?_⟩
    let := (hQfree i).1
    exact ⟨(hQfree i).2, inferInstance⟩
  refine ⟨⟨(associatedComplex R).obj Q, strictPerfect_associated R hQ⟩, ⟨?_⟩⟩
  exact ((principalRestrictionAssociatedComplexIso R r).app Q).symm ≪≫
    (associatedComplex S).mapIso eQ ≪≫ associatedSectionsIso S P.property

/-- Such targets belong to the honest essential image of the original strict
restriction functor, before taking any K-theory group or adding summands. -/
theorem principalStrictRestrict_essImage_of_free_sections (R : CommRingCat.{u}) (r : R)
    (P : StrictPerfect (Spec (.of (Localization.Away r))))
    (hfree : ∀ i, Module.Free (Localization.Away r)
      (((sectionsComplex (.of (Localization.Away r))).obj P.obj).X i)) :
    (strictRestrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).essImage P
      := by
  obtain ⟨Q, ⟨e⟩⟩ := exists_principal_strict_extension_of_free_sections R r P hfree
  exact ⟨Q, ⟨ObjectProperty.isoMk _ e⟩⟩

end Quillen.PerfectComplexes.Affine
