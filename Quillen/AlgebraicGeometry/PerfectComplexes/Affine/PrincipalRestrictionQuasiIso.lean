/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.DerivedComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.LocalRestriction
public import Quillen.AlgebraicGeometry.PerfectComplexes.DerivedHom.OpenUnion
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.FinitePrincipalCohomologicalDimension

/-!
# Detecting original associated-sheaf quasi-isomorphisms on principal charts

The actual natural isomorphism from a contained principal chart to module
localization identifies original chain maps, so weakness on an open implies
weakness at every contained principal localization. Conversely, a finite
principal family whose literal union is the chosen open detects weakness.
The family need not cover Spec R; arbitrary rings and empty opens are allowed.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.Affine
open Quillen.ModuleComplex.PrincipalLocalization

/-- The entire chart comparison, retaining its naturality on original module chain maps. -/
def principalChartAssociatedComplexNatIso (R : CommRingCat.{u}) {U : Scheme.{u}}
    (j : U ⟶ Spec R) [IsOpenImmersion j] (r : R)
    (k : Spec (.of (Localization.Away r)) ⟶ U) [IsOpenImmersion k]
    (hk : k ≫ j = AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r) :
    associatedComplex R ⋙ restrict j ⋙ restrict k ≅
      localize r (.up ℤ) ⋙ associatedComplex (.of (Localization.Away r)) :=
  Functor.isoWhiskerLeft (associatedComplex R) (restrictCompIso k j) ≪≫
    Functor.isoWhiskerLeft (associatedComplex R) (eqToIso (restrict_congr hk)) ≪≫
      (principalRestrictionAssociatedComplexIso R r).symm

lemma quasiIso_principalChart_iff (R : CommRingCat.{u}) {U : Scheme.{u}}
    (j : U ⟶ Spec R) [IsOpenImmersion j] (r : R)
    (k : Spec (.of (Localization.Away r)) ⟶ U) [IsOpenImmersion k]
    (hk : k ≫ j = AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)
    {P B : ModuleComplex R} (f : P ⟶ B) :
    QuasiIso ((restrict k).map ((restrict j).map ((associatedComplex R).map f))) ↔
      QuasiIso ((localize r (.up ℤ)).map f) := by
  let e := principalChartAssociatedComplexNatIso R j r k hk
  rw [← quasiIso_associated_iff (.of (Localization.Away r))]
  exact quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (e.app P) (e.app B) (e.hom.naturality f).symm)

lemma quasiIso_localize_of_restrict_associated (R : CommRingCat.{u})
    (W : (Spec R).Opens) {P B : ModuleComplex R} (f : P ⟶ B)
    [QuasiIso ((restrict W.ι).map ((associatedComplex R).map f))]
    (r : R) (hr : PrimeSpectrum.basicOpen r ≤ W) : QuasiIso ((localize r (.up ℤ)).map f) := by
  let j := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r
  have hjW : Set.range j ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, Scheme.Hom.opensRange_localizationAway r]
    exact hr
  let k := IsOpenImmersion.lift W.ι j hjW
  have hk : k ≫ W.ι = j := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (k ≫ W.ι) := by rw [hk]; infer_instance
  have : IsOpenImmersion k := IsOpenImmersion.of_comp k W.ι
  exact (quasiIso_principalChart_iff R W.ι r k hk f).mp inferInstance

lemma quasiIso_restrict_associated_of_principalUnion (R : CommRingCat.{u})
    (W : (Spec R).Opens) (s : Finset R) (hs : Quillen.SheafCohomology.principalUnion R s = W)
    {P B : ModuleComplex R} (f : P ⟶ B)
    (hf : ∀ r ∈ s, QuasiIso ((localize r (.up ℤ)).map f)) :
    QuasiIso ((restrict W.ι).map ((associatedComplex R).map f)) := by
  have hsr (r : s) : PrimeSpectrum.basicOpen r.val ≤ W := by
    rw [← hs]
    exact Quillen.SheafCohomology.basicOpen_le_principalUnion R r.property
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
    obtain ⟨r, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨hr, hx⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
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
  apply quasiIso_of_openImmersionCover _
    (fun r : s => Spec (.of (Localization.Away r.val))) k hcover
  intro r
  exact (quasiIso_principalChart_iff R W.ι r.val (k r) (hk r) f).mpr (hf r.val r.property)

end Quillen.PerfectComplexes.Affine
