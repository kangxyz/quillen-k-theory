/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BoundedDerivedComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.PrincipalPerfectDescent

/-!
# Affine strictification of original locally-perfect complexes

Every locally-perfect complex of arbitrary module sheaves on `Spec R` has a
genuine bounded finite-projective module representative, and hence a strict
perfect sheaf representative, in the original `toDerived` category.

The proof refines actual local strict models to a finite principal cover,
uses the original bounded derived comparison to recover genuine localized
module models, chooses a common lower term bound, and applies finite cone
induction. No noetherianity or termwise quasicoherence is assumed. Affine
compactness is used through the proved cohomological boundedness theorem.
The conclusion for arbitrary ambient sheaf complexes is a derived
isomorphism, not an asserted direct chain quasi-isomorphism.

See Stacks Project Tags 08EB and 066D for the corresponding affine
perfectness and finite-attachment arguments.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open HomologicalComplex TopologicalSpace

namespace Quillen.PerfectComplexes.Affine
attribute [local instance] standardDerivedModules standardDerivedSheaves

/-- Refine an original local strict model to an actual principal neighborhood of a specified affine
  point. -/
lemma exists_principal_strict_model_near (R : CommRingCat.{u})
    {K : Complex (Spec R)} (hK : locallyPerfect (Spec R) K) (x : Spec R) :
    ∃ r : R, x ∈ PrimeSpectrum.basicOpen r ∧
      ∃ P : StrictPerfect (Spec (CommRingCat.of (Localization.Away r))),
        Nonempty ((toDerived _).obj ((restrict
          (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj K) ≅
          (toDerived _).obj P.obj) := by
  obtain ⟨U, hxU, P, ⟨eP⟩⟩ := hK x
  obtain ⟨_, ⟨r, rfl⟩, hxr, hrU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
  let j := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r
  have hjU : Set.range j ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_localizationAway r]
    exact hrU
  let k := IsOpenImmersion.lift U.ι j hjU
  have hk : k ≫ U.ι = j := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (k ≫ U.ι) := by rw [hk]; infer_instance
  have : IsOpenImmersion k := IsOpenImmersion.of_comp k U.ι
  let e : restrict U.ι ⋙ restrict k ≅ restrict j :=
    restrictCompIso k U.ι ≪≫ eqToIso (restrict_congr hk)
  exact ⟨r, hxr, ⟨(restrict k).obj P.obj, strictPerfect_restrict k P.property⟩,
    ⟨(toDerived _).mapIso (e.app K).symm ≪≫ restrictDerivedIso k eP⟩⟩

/-- Affine compactness extracts a finite principal cover with original restricted strict models. -/
lemma exists_finite_principal_strict_models (R : CommRingCat.{u})
    {K : Complex (Spec R)} (hK : locallyPerfect (Spec R) K) :
    ∃ s : Finset R, Ideal.span (s : Set R) = ⊤ ∧
      ∀ r : s, ∃ P : StrictPerfect (Spec (CommRingCat.of (Localization.Away r.val))),
        Nonempty ((toDerived _).obj ((restrict
          (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r.val)).obj K) ≅
          (toDerived _).obj P.obj) := by
  classical
  let S : Set R := {r | ∃ P : StrictPerfect (Spec (CommRingCat.of (Localization.Away r))),
    Nonempty ((toDerived _).obj ((restrict
      (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj K) ≅
      (toDerived _).obj P.obj)}
  have hS : Ideal.span S = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff']
    apply top_unique
    intro x _
    obtain ⟨r, hxr, P, e⟩ := exists_principal_strict_model_near R hK x
    exact Opens.mem_iSup.mpr ⟨r, Opens.mem_iSup.mpr ⟨⟨P, e⟩, hxr⟩⟩
  obtain ⟨s, hsS, hs⟩ := (Ideal.span_eq_top_iff_finite S).mp hS
  exact ⟨s, hs, fun r => hsS r.property⟩


/-- Lift a bounded isomorphism under the original fully faithful affine derived comparison. -/
def associatedDerivedIsoLiftBounded (R : CommRingCat.{u})
    (K L : DerivedCategory (ModuleCat.{u} R)) (a b c d : ℤ)
    [K.IsGE a] [K.IsLE b] [L.IsGE c] [L.IsLE d]
    (e : (associatedDerived R).obj K ≅ (associatedDerived R).obj L) : K ≅ L := by
  let A : DerivedCategory.Bounded (ModuleCat.{u} R) := ⟨K, ⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩⟩
  let B : DerivedCategory.Bounded (ModuleCat.{u} R) := ⟨L, ⟨⟨c, inferInstance⟩, ⟨d, inferInstance⟩⟩⟩
  exact DerivedCategory.Bounded.ι.mapIso ((associatedBoundedDerived R).preimageIso (X := A) (Y := B)
    e)

/-- The lifted isomorphism has the prescribed image under the original derived associated-sheaf map.
-/
lemma associatedDerivedIsoLiftBounded_hom (R : CommRingCat.{u})
    (K L : DerivedCategory (ModuleCat.{u} R)) (a b c d : ℤ)
    [K.IsGE a] [K.IsLE b] [L.IsGE c] [L.IsLE d]
    (e : (associatedDerived R).obj K ≅ (associatedDerived R).obj L) :
    (associatedDerived R).map (associatedDerivedIsoLiftBounded R K L a b c d e).hom = e.hom := by
  exact (associatedBoundedDerived R).map_preimage
    (X := ⟨K, ⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩⟩)
    (Y := ⟨L, ⟨⟨c, inferInstance⟩, ⟨d, inferInstance⟩⟩⟩) e.hom

/-- Original affine local perfection and bounded comparison yield genuine derived models of the
  actual localized module complexes. -/
lemma exists_finite_principal_module_strict_models (R : CommRingCat.{u})
    (K : ModuleComplex R) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : locallyPerfect (Spec R) ((associatedComplex R).obj K)) :
    ∃ s : Finset R, Ideal.span (s : Set R) = ⊤ ∧
      ∀ r : s, ∃ P : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
        moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) P ∧
        Nonempty (DerivedCategory.Q.obj ((Quillen.ModuleComplex.PrincipalLocalization.localize r.val
          (.up ℤ)).obj K) ≅
          DerivedCategory.Q.obj P) := by
  obtain ⟨s, hs, hmodels⟩ := exists_finite_principal_strict_models R hK
  refine ⟨s, hs, fun r => ?_⟩
  obtain ⟨Q, ⟨eQ⟩⟩ := hmodels r
  let S := CommRingCat.of (Localization.Away r.val)
  let P : ModuleComplex S := (sectionsComplex S).obj Q.obj
  have hP : moduleStrictPerfect S P := moduleStrictPerfect_sections S Q.property
  obtain ⟨⟨c, d, hcd⟩, hterms⟩ := hP
  have : P.IsStrictlyGE c := (CochainComplex.isStrictlyGE_iff P c).mpr (fun i hi => hcd i (Or.inl
    hi))
  have : P.IsStrictlyLE d := (CochainComplex.isStrictlyLE_iff P d).mpr (fun i hi => hcd i (Or.inr
    hi))
  let K' : ModuleComplex S := (Quillen.ModuleComplex.PrincipalLocalization.localize r.val (.up
    ℤ)).obj K
  let F := ModuleCat.localizedModuleFunctor (Submonoid.powers r.val)
  have : K'.IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro i hi
    exact (K.exactAt_of_isGE a i hi).map F
  have : K'.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    exact (K.exactAt_of_isLE b i hi).map F
  let e : (associatedDerived S).obj (DerivedCategory.Q.obj K') ≅
      (associatedDerived S).obj (DerivedCategory.Q.obj P) :=
    (associatedDerivedFactors S).app K' ≪≫
      (toDerived _).mapIso ((principalRestrictionAssociatedComplexIso R r.val).app K) ≪≫
      eQ ≪≫ (toDerived _).mapIso (associatedSectionsIso S Q.property).symm ≪≫
      ((associatedDerivedFactors S).app P).symm
  exact ⟨P, ⟨⟨c, d, hcd⟩, hterms⟩,
    ⟨associatedDerivedIsoLiftBounded S (DerivedCategory.Q.obj K') (DerivedCategory.Q.obj P) a b c d
      e⟩⟩

end Quillen.PerfectComplexes.Affine

namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] standardDerivedModules standardDerivedSheaves

/-- A finite principal family of actual strict models has a common lower term bound, including the
  empty family. -/
lemma exists_uniform_lower_principal_models (R : CommRingCat.{u})
    (K : ModuleComplex R) (s : Finset R)
    (hlocal : ∀ r : s, ∃ P : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
      moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) P ∧
      Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P)) :
    ∃ a : ℤ, ∀ r : s, ∃ P : ModuleComplex (CommRingCat.of (Localization.Away r.val)),
      moduleStrictPerfect (CommRingCat.of (Localization.Away r.val)) P ∧
      (∀ i, i < a → IsZero (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P) :=
        by
  classical
  choose P hp he using hlocal
  have hb (r : s) : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero ((P r).X i) := (hp r).1
  choose a b hb using hb
  obtain ⟨c, hc⟩ := (Set.finite_range a).bddBelow
  exact ⟨c, fun r => ⟨P r, hp r, fun i hi => hb r i (Or.inl (lt_of_lt_of_le hi
    (hc (Set.mem_range_self r)))), he r⟩⟩

/-- A cohomologically bounded module complex whose associated sheaf complex is locally perfect has a
  global finite-projective derived model. -/
lemma finiteProjectiveDerived_of_locallyPerfect_associated (R : CommRingCat.{u})
    (K : ModuleComplex R) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : locallyPerfect (Spec R) ((associatedComplex R).obj K)) :
    finiteProjectiveDerivedObjects R (DerivedCategory.Q.obj K) := by
  obtain ⟨s, hs, hlocal⟩ := exists_finite_principal_module_strict_models R K a b hK
  obtain ⟨c, hc⟩ := exists_uniform_lower_principal_models R K s hlocal
  exact finiteProjectiveDerived_of_principal_models R K c b s hs hc

/-- Original affine local perfection gives a genuine bounded finite-projective
module representative, over an arbitrary commutative ring. -/
lemma locallyPerfect_exists_moduleStrictPerfect_representative (R : CommRingCat.{u})
    {K : Complex (Spec R)} (hK : locallyPerfect (Spec R) K) :
    ∃ P : ModuleComplex R, moduleStrictPerfect R P ∧
      Nonempty ((toDerived (Spec R)).obj ((associatedComplex R).obj P) ≅
        (toDerived (Spec R)).obj K) := by
  obtain ⟨L, a, b, hge, hle, ⟨eL⟩⟩ := locallyPerfect_exists_bounded_module_representative R hK
  have hL : locallyPerfect (Spec R) ((associatedComplex R).obj L) :=
    (locallyPerfect_iff_of_derivedIso eL).mpr hK
  obtain ⟨P, hP, ⟨eP⟩⟩ := finiteProjectiveDerived_of_locallyPerfect_associated R L a b hL
  exact ⟨P, hP, ⟨((associatedDerivedFactors R).app P).symm ≪≫
    (associatedDerived R).mapIso eP ≪≫ (associatedDerivedFactors R).app L ≪≫ eL⟩⟩

/-- Every affine locally-perfect complex has a strict-perfect representative
in the original derived category of all module sheaves. -/
lemma locallyPerfect_exists_strictPerfect_representative (R : CommRingCat.{u})
    {K : Complex (Spec R)} (hK : locallyPerfect (Spec R) K) :
    ∃ P : StrictPerfect (Spec R),
      Nonempty ((toDerived (Spec R)).obj P.obj ≅ (toDerived (Spec R)).obj K) := by
  obtain ⟨P, hP, e⟩ := locallyPerfect_exists_moduleStrictPerfect_representative R hK
  exact ⟨⟨(associatedComplex R).obj P, strictPerfect_associated R hP⟩, e⟩

end Quillen.PerfectComplexes.Affine
