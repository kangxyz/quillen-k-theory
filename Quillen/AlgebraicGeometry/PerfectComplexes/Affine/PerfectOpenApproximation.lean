/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenModuleReconstruction
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.Strictification
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.FinitePrincipalRemainder

/-!
# Arbitrarily low actual approximations of original perfect complexes on qc opens

Every original locally-perfect complex on a quasi-compact open W of Spec R
has an actual global bounded finite-projective approximation to its bounded
module representative. The ORIGINAL restricted cone is a derived single on
its finite locally free homology sheaf, in a degree no larger than any requested
cutoff. There are no supplied local finite-projective models: a genuine finite
principal cover, actual affine strictification on each chart, and a common
lower term bound construct those models.

The target remains the actual bounded module reconstruction of the original
input, related to it by the proved original derived isomorphism. The source
and chain map are global; finite local freeness of the cone homology is asserted
only on W. No splitting of the residual triangle, ambient projectivity of its
homology, or full localization theorem is inferred here. Arbitrarily small
cutoffs are retained for the subsequent genuine Ext-vanishing argument.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace HomologicalComplex
universe u
namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization
attribute [local instance] standardDerivedModules standardDerivedSheaves

/-- A principal chart contained in the chosen open has an actual finite-projective
module model, obtained by full affine strictification of its original restriction. -/
lemma exists_principal_module_model_on_open (R : CommRingCat.{u})
    (W : (Spec R).Opens) (K : ModuleComplex R) (a b : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : locallyPerfect W.toScheme ((restrict W.ι).obj ((associatedComplex R).obj K)))
    (r : R) (hr : PrimeSpectrum.basicOpen r ≤ W) :
    ∃ P : ModuleComplex (.of (Localization.Away r)), moduleStrictPerfect _ P ∧
      Nonempty (DerivedCategory.Q.obj ((localize r (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P) := by
  let j := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r
  have hjW : Set.range j ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_localizationAway r]
    exact hr
  let k := IsOpenImmersion.lift W.ι j hjW
  have hk : k ≫ W.ι = j := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (k ≫ W.ι) := by rw [hk]; infer_instance
  have : IsOpenImmersion k := IsOpenImmersion.of_comp k W.ι
  let S := CommRingCat.of (Localization.Away r)
  let L : ModuleComplex S := (localize r (.up ℤ)).obj K
  have hL : locallyPerfect (Spec S) ((associatedComplex S).obj L) :=
    locallyPerfect_of_iso (principalChartAssociatedComplexIso R W.ι r k hk K)
      (locallyPerfect_restrict k hK)
  have hLa : L.IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro n hn
    exact (K.exactAt_of_isGE a n hn).map (ModuleCat.localizedModuleFunctor (Submonoid.powers r))
  have hLb : L.IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro n hn
    exact (K.exactAt_of_isLE b n hn).map (ModuleCat.localizedModuleFunctor (Submonoid.powers r))
  obtain ⟨P, hP, ⟨e⟩⟩ := finiteProjectiveDerived_of_locallyPerfect_associated S L a b hL
  exact ⟨P, hP, ⟨e.symm⟩⟩

/-- Quasi-compactness gives a genuine finite principal cover of the chosen open,
including the empty open. The family need not cover the affine ambient scheme. -/
lemma exists_finite_principal_cover (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) :
    ∃ s : Finset R, Quillen.SheafCohomology.principalUnion R s = W := by
  classical
  obtain ⟨ι, _, q, hq⟩ := PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact W hW
  let := Fintype.ofFinite ι
  let s : Finset R := Finset.univ.image q
  refine ⟨s, ?_⟩
  rw [hq]
  apply le_antisymm
  · refine iSup₂_le fun z hz => ?_
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact le_iSup (fun i => PrimeSpectrum.basicOpen (q i)) i
  · exact iSup_le fun i => Quillen.SheafCohomology.basicOpen_le_principalUnion R
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)


/-- Any bounded module complex perfect only on W has an actual global strict
approximation whose original vector-bundle remainder lies below the requested cutoff. -/
lemma exists_strict_approximation_on_compact_open (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (K : ModuleComplex R) (a b cutoff : ℤ) [K.IsGE a] [K.IsLE b]
    (hK : locallyPerfect W.toScheme ((restrict W.ι).obj ((associatedComplex R).obj K))) :
    ∃ (c : ℤ), c ≤ cutoff ∧ ∃ (P : ModuleComplex R) (_ : moduleStrictPerfect R P) (f : P ⟶ K),
      let D := (restrict W.ι).obj ((associatedComplex R).obj (CochainComplex.mappingCone f))
      AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree W.toScheme (D.homology c) ∧ D.IsGE c ∧
        D.IsLE c ∧
        Nonempty ((toDerived W.toScheme).obj D ≅ (toDerived W.toScheme).obj
          ((CochainComplex.singleFunctor W.toScheme.Modules c).obj (D.homology c))) := by
  classical
  obtain ⟨s, hs⟩ := exists_finite_principal_cover R W hW
  have hsr (r : s) : PrimeSpectrum.basicOpen r.val ≤ W := by
    rw [← hs]
    exact Quillen.SheafCohomology.basicOpen_le_principalUnion R r.property
  have hlocal (r : s) := exists_principal_module_model_on_open R W K a b hK r.val (hsr r)
  obtain ⟨c₀, hc₀⟩ := exists_uniform_lower_principal_models R K s hlocal
  let c := min c₀ cutoff
  have hc (r : s) : ∃ P : ModuleComplex (.of (Localization.Away r.val)),
      moduleStrictPerfect _ P ∧ (∀ i, i < c → IsZero (P.X i)) ∧
      Nonempty (DerivedCategory.Q.obj ((localize r.val (.up ℤ)).obj K) ≅ DerivedCategory.Q.obj P) :=
        by
    obtain ⟨P, hP, hb, he⟩ := hc₀ r
    exact ⟨P, hP, fun i hi => hb i (lt_of_lt_of_le hi (min_le_left _ _)), he⟩
  have hjW (r : s) : Set.range (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R
    r.val) ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_localizationAway
      r.val]
    exact hsr r
  let k (r : s) := IsOpenImmersion.lift W.ι
    (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r.val) (hjW r)
  have hk (r : s) : k r ≫ W.ι = AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r.val
    :=
    IsOpenImmersion.lift_fac _ _ _
  have hki (r : s) : IsOpenImmersion (k r) := by
    have : IsOpenImmersion (k r ≫ W.ι) := by rw [hk]; infer_instance
    exact IsOpenImmersion.of_comp (k r) W.ι
  have hcover (x : W.toScheme) : ∃ r : s, ∃ y, k r y = x := by
    have hx : W.ι x ∈ Quillen.SheafCohomology.principalUnion R s := by
      rw [hs]
      exact x.property
    obtain ⟨r, hx⟩ := Opens.mem_iSup.mp hx
    obtain ⟨hr, hx⟩ := Opens.mem_iSup.mp hx
    have hx' : W.ι x ∈ Set.range (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)
      := by
      rw [← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_localizationAway r]
      exact hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨⟨r, hr⟩, y, ?_⟩
    apply W.ι.isOpenEmbedding.injective
    change (k ⟨r, hr⟩ ≫ W.ι) y = W.ι x
    rw [hk]
    exact hy
  have hbound (r : s) : CochainComplex.IsLE ((localize r.val (.up ℤ)).obj K) b := by
    rw [CochainComplex.isLE_iff]
    intro n hn
    exact (K.exactAt_of_isLE b n hn).map (ModuleCat.localizedModuleFunctor (Submonoid.powers r.val))
  obtain ⟨P, hP, f, hf⟩ :=
    exists_moduleStrictPerfect_approximation_with_vectorBundle_remainder R W.ι K c b s
      k hk hcover hbound hc
  exact ⟨c, min_le_right _ _, P, hP, f, hf⟩


/-- Original perfect input on a qc affine open admits an actual bounded module
roof and global finite-projective approximation, with arbitrarily low original
vector-bundle remainder. No local-model or splitting premise remains. -/
lemma locallyPerfect_exists_original_strict_approximation (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (E : Complex W.toScheme) (hE : locallyPerfect W.toScheme E) (cutoff : ℤ) :
    ∃ (K : ModuleComplex R) (a b : ℤ) (P : ModuleComplex R) (n : ℤ) (f : P ⟶ K),
      K.IsStrictlyGE a ∧ K.IsStrictlyLE b ∧ moduleStrictPerfect R P ∧ n ≤ cutoff ∧
      Nonempty ((toDerived W.toScheme).obj ((restrict W.ι).obj ((associatedComplex R).obj K)) ≅
        (toDerived W.toScheme).obj E) ∧
      let D := (restrict W.ι).obj ((associatedComplex R).obj (CochainComplex.mappingCone f))
      AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree W.toScheme (D.homology n) ∧ D.IsGE n ∧
        D.IsLE n ∧
        Nonempty ((toDerived W.toScheme).obj D ≅ (toDerived W.toScheme).obj
          ((CochainComplex.singleFunctor W.toScheme.Modules n).obj (D.homology n))) := by
  obtain ⟨K, a, b, hKa, hKb, ⟨eK⟩⟩ :=
    locallyPerfect_exists_bounded_module_open_representative R W hW hE
  have hK : locallyPerfect W.toScheme ((restrict W.ι).obj ((associatedComplex R).obj K)) :=
    (locallyPerfect_iff_of_derivedIso eK).mpr hE
  obtain ⟨n, hn, P, hP, f, hf⟩ := exists_strict_approximation_on_compact_open R W hW K a b cutoff hK
  exact ⟨K, a, b, P, n, f, hKa, hKb, hP, hn, ⟨eK⟩, hf⟩

end Quillen.PerfectComplexes.Affine
