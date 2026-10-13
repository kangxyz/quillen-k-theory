/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.Excision
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.DerivedExcision
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.RestrictionComparison

/-! # Supported perfect-complex excision consumers -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
universe u
namespace QuillenTest.SupportExcision
open Quillen.PerfectComplexes Quillen.Waldhausen
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (T : X.Opens)
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ T)

/-- The genuine inverse sends a supported complex to the actual extended
complex, and its restriction is the original source via the original unit. -/
theorem original_extension_restriction (K : (perfectSupported (j ⁻¹ᵁ T).ι).FullSubcategory) :
    ((perfectSupportedExtensionByZero j T hcover).obj K).obj = (extensionByZero j).obj K.obj ∧
    ((perfectSupportedExcisionAdjunction j T hcover).unit.app K).hom =
      (extensionByZeroAdjunction j).unit.app K.obj ∧
    IsIso (((perfectSupportedExcisionAdjunction j T hcover).unit.app K).hom) := by
  refine ⟨rfl,rfl,?_⟩
  change IsIso ((extensionByZeroAdjunction j).unit.app K.obj)
  infer_instance

/-- The actual global counit, not a selected replacement map, induces an
isomorphism on each original homology module sheaf. -/
theorem original_counit_homology (K : (perfectSupported T.ι).FullSubcategory) (n : ℤ) :
    ((perfectSupportedExcisionAdjunction j T hcover).counit.app K).hom =
      (extensionByZeroAdjunction j).counit.app K.obj ∧
    IsIso ((homologyFunctor X.Modules (.up ℤ) n).map
      (((perfectSupportedExcisionAdjunction j T hcover).counit.app K).hom)) := by
  have : QuasiIso ((extensionByZeroAdjunction j).counit.app K.obj) :=
    extensionByZero_supported_counit_quasiIso j T hcover K.property
  refine ⟨rfl,?_⟩
  change IsIso ((homologyFunctor X.Modules (.up ℤ) n).map
    ((extensionByZeroAdjunction j).counit.app K.obj))
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance

/-- The entire inverse natural transformation preserves every actual supported
chain arrow, with the unchanged original counit on each endpoint. -/
theorem original_counit_naturality {K L : (perfectSupported T.ι).FullSubcategory} (f : K ⟶ L) :
    (extensionByZero j).map ((restrict j).map f.hom) ≫
        (extensionByZeroAdjunction j).counit.app L.obj =
      (extensionByZeroAdjunction j).counit.app K.obj ≫ f.hom := by
  exact (extensionByZeroAdjunction j).counit.naturality f.hom

/-- Both homotopy inverses are the original realization maps. -/
theorem original_realization_inverse :
    ((deloopingMap (perfectSupportedExtensionByZero_exact j T hcover)).hom.comp
      (deloopingMap (perfectSupportedRestrict_exact j T)).hom).Homotopic
        (ContinuousMap.id (perfectSupportedWaldhausen T.ι).Delooping) ∧
    ((deloopingMap (perfectSupportedRestrict_exact j T)).hom.comp
      (deloopingMap (perfectSupportedExtensionByZero_exact j T hcover)).hom).Homotopic
        (ContinuousMap.id (perfectSupportedWaldhausen (j ⁻¹ᵁ T).ι).Delooping) :=
  ⟨(perfectSupportedExcisionRealizationHomotopyEquiv j T hcover).left_inv,
    (perfectSupportedExcisionRealizationHomotopyEquiv j T hcover).right_inv⟩

/-- Degree zero has a unique original lift, explicitly the actual j! K-map. -/
theorem original_zero_unique_lift (y : PerfectSupportedK (j ⁻¹ᵁ T).ι 0) :
    perfectSupportedKRestrict j T 0
        (KMap (perfectSupportedExtensionByZero_exact j T hcover) 0 y) = y ∧
    ∀ x : PerfectSupportedK T.ι 0, perfectSupportedKRestrict j T 0 x = y →
      x = KMap (perfectSupportedExtensionByZero_exact j T hcover) 0 y := by
  refine ⟨perfectSupportedKRestrict_extensionByZero_rightInverse j T hcover 0 y,?_⟩
  intro x hx
  rw [← hx]
  exact (perfectSupportedKRestrict_extensionByZero_leftInverse j T hcover 0 x).symm

include hcover in
/-- The old public pair pullback is itself bijective in every degree; compactness
is needed only to use that original public model comparison. -/
theorem original_public_pair_excision [CompactSpace U] [CompactSpace X] (n : ℕ) :
    Function.Bijective (perfectSupportedKPullback (qcSupportRestrictionPair j T) n) := by
  rw [← perfectSupportedKRestrict_eq_pullback]
  exact perfectSupportedKRestrict_bijective_of_cover j T hcover n

/-- The edge case with the auxiliary open equal to the whole scheme has
no condition on the open immersion; its source is the actual acyclic model. -/
theorem top_auxiliary_open (n : ℕ) :
    Function.Bijective (perfectSupportedKRestrict j (⊤ : X.Opens) n) :=
  perfectSupportedKRestrict_bijective_of_cover j ⊤ (fun _ => Or.inr trivial) n

include hcover in
/-- An arbitrary original target map extends from the supported local source
with a literal chain triangle and the original unit comparison. -/
theorem original_target_map_extension {A : Complex U} (hA : perfectSupported (j ⁻¹ᵁ T).ι A)
    {L : Complex X} (f : A ⟶ (restrict j).obj L) :
    ∃ (M : Complex X) (e : A ≅ (restrict j).obj M) (d : M ⟶ L),
      perfectSupported T.ι M ∧ e.hom ≫ (restrict j).map d = f := by
  exact ⟨(extensionByZero j).obj A, asIso ((extensionByZeroAdjunction j).unit.app A),
    extensionByZeroMap j f, perfectSupported_extensionByZero_of_cover j T hcover hA,
    extensionByZeroMap_restrict j f⟩

include hcover in
/-- Every original local derived arrow has a unique original global lift;
the all-sheaf target has no perfection or quasicoherence assumption. -/
theorem arbitrary_derived_target_unique_lift {K : Complex X} (hK : perfectSupported T.ι K)
    (L : Complex X)
    (f : (toDerived U).obj ((restrict j).obj K) ⟶ (toDerived U).obj ((restrict j).obj L)) :
    ∃! g : (toDerived X).obj K ⟶ (toDerived X).obj L, restrictDerivedHom j g = f := by
  refine ⟨(perfectSupportedDerivedHomEquiv j T hcover hK L).symm f, by simp, ?_⟩
  intro g hg
  apply (restrictDerivedHom_bijective_of_supported_cover j T hcover hK L).injective
  simpa using hg

/-- Inverse excision retains arbitrary original derived postcomposition. -/
theorem arbitrary_derived_target_naturality {K : Complex X} (hK : perfectSupported T.ι K)
    (L L' : Complex X)
    (f : (toDerived U).obj ((restrict j).obj K) ⟶ (toDerived U).obj ((restrict j).obj L))
    (b : (toDerived X).obj L ⟶ (toDerived X).obj L') :
    (perfectSupportedDerivedHomEquiv j T hcover hK L).symm f ≫ b =
      (perfectSupportedDerivedHomEquiv j T hcover hK L').symm (f ≫ restrictDerivedHom j b) :=
  perfectSupportedDerivedHomEquiv_symm_postcomp j T hcover hK L f b

end QuillenTest.SupportExcision
