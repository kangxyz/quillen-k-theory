/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.Sheaves.BasisExactness
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Epimorphisms
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Original module-sheaf quasi-isomorphisms detected on a basis

The genuine underlying abelian-sheaf functor is faithful and exact, so the
section-basis criterion applies to original complexes of all module sheaves.
For an affine scheme its actual principal basic opens form the needed basis.
No termwise quasicoherence, injectivity or cohomological bound is required.
-/
@[expose] public section



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts

/-- Forget the module structure degreewise, retaining the underlying complex of sheaves. -/
abbrev underlyingSheafComplex (X : Scheme.{u}) :=
  (SheafOfModules.toSheaf X.ringCatSheaf).mapHomologicalComplex (.up ℤ)

/-- Take sections on the specified open, degreewise in the underlying sheaf complex. -/
abbrev sectionsComplex (X : Scheme.{u}) (U : X.Opens) :=
  underlyingSheafComplex X ⋙
    (TopCat.Sheaf.sectionsFunctor U).mapHomologicalComplex (.up ℤ)

lemma quasiIso_of_sections_on_basis {X : Scheme.{u}}
    {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L)
    {B : Set X.Opens} (hB : Opens.IsBasis B)
    (hf : ∀ U ∈ B, QuasiIso ((sectionsComplex X U).map f)) : QuasiIso f := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  let : F.Additive := ⟨by intros; rfl⟩
  let : PreservesFiniteColimits F := ⟨fun _ => inferInstance⟩
  let : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf))
  let : F.ReflectsIsomorphisms := ⟨fun f hf => by
    let := hf
    have : Mono f := F.mono_of_mono_map inferInstance
    have : Epi f := F.epi_of_epi_map inferInstance
    exact isIso_of_mono_of_epi f⟩
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f F).mp
  exact TopCat.Sheaf.quasiIso_of_sections_on_basis
    ((underlyingSheafComplex X).map f) hB hf

lemma quasiIso_of_sections_on_principals (R : CommRingCat.{u})
    {K L : CochainComplex (Spec R).Modules ℤ} (f : K ⟶ L)
    (hf : ∀ r : R, QuasiIso ((sectionsComplex (Spec R) (PrimeSpectrum.basicOpen r)).map f)) :
    QuasiIso f := by
  apply quasiIso_of_sections_on_basis f PrimeSpectrum.isBasis_basic_opens
  rintro U ⟨r, rfl⟩
  exact hf r

end AlgebraicGeometry.Scheme.Modules
