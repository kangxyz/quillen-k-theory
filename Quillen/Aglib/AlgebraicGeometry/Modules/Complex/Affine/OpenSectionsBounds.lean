/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Quillen.Aglib.AlgebraicGeometry.Cohomology.Affine.FinitePrincipalDimension
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.Affine.PrincipalSections
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction

public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
/-!
# Geometric bounds for original sections on compact affine opens

A lower-bounded injective complex on `Spec R` has an upper cohomological
bound on sections over a finite union of principal opens contained in `W`,
provided its original restriction to `W` has quasicoherent homology and upper
bound `b`. The bound is exactly `b + s.card - 1`. There is no additional
acyclicity premise on principal sections: the literal affine derived counit,
exact faithful tilde, and actual restriction of injectives prove those bounds.

Only homology on `W` is assumed quasicoherent; the ambient complex, its terms,
and its homology away from `W` are unrestricted. A compact `W` yields an upper
bound on its actual R-module sections. The final construction retains the
original weak map from any bounded-QC complex on `W` into its ambient injective
model, and proves boundedness of its actual sections with the exact requested
lower term bound. It does not yet identify the associated sheaf of those
sections with the complex on `W`, or assert ambient perfection.

All coefficient rings are arbitrary. Empty principal families and empty opens
are included. Compactness is explicit when extracting a finite principal cover.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
  Opposite
namespace Quillen.PerfectComplexes.Affine
local instance openSectionsBoundsGlobalSections_additive (R : CommRingCat.{u}) (r : R) :
    (moduleSpecΓFunctor (R := CommRingCat.of (Localization.Away r))).Additive :=
  AlgebraicGeometry.Scheme.Modules.moduleSpecΓFunctor_additive _

/-- The actual affine counit reflects the upper cohomology bound to original sections. -/
lemma isLE_sections_of_injective {R : CommRingCat.{u}}
    (I : CochainComplex (Spec R).Modules ℤ) (a b : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) [I.IsLE b] :
    ((sectionsComplex R).obj I).IsLE b := by
  let := quasiIso_associatedSectionsCounit I a hbound hinj hqc
  rw [CochainComplex.isLE_iff]
  intro n hn
  apply Functor.reflects_exact_of_faithful (tilde.functor R)
    (((sectionsComplex R).obj I).sc n)
  exact (exactAt_iff_of_quasiIsoAt (associatedSectionsCounit R I) n).mpr
    (I.exactAt_of_isLE b n hn)

/-- Underlying actual R-module sheaves retain the flasque restriction property. -/
lemma isFlasque_modulesSpecToSheaf {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [TopCat.Presheaf.IsFlasque M.presheaf] :
    TopCat.Presheaf.IsFlasque (modulesSpecToSheaf.obj M).obj where
  epi {U V} f := by
    rw [ModuleCat.epi_iff_surjective]
    exact (AddCommGrpCat.epi_iff_surjective (M.presheaf.map f)).mp inferInstance

/-- Original R-module sections on a principal open inherit the genuine bound
of the restricted sheaf complex by affine acyclicity. -/
lemma isLE_principalSections_of_injective {R : CommRingCat.{u}}
    (I : CochainComplex (Spec R).Modules ℤ)
    (a b : ℤ) (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n)) (r : R)
    (hqc : ∀ n, (((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj
      I).homology n).IsQuasicoherent)
    [((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj I).IsLE b] :
    CochainComplex.IsLE (((affineSectionsAt R (PrimeSpectrum.basicOpen r)).mapHomologicalComplex
      (.up ℤ)).obj I) b := by
  let j := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r
  let J := (restrict j).obj I
  have hJ : J.IsLE b := inferInstance
  have hb (n : ℤ) (hn : n < a) : IsZero (J.X n) :=
    (Scheme.Modules.restrictFunctor j).map_isZero (hbound n hn)
  have hi (n : ℤ) : Injective (J.X n) := by
    let := hinj n
    exact AlgebraicGeometry.Scheme.Modules.injective_restrict j (I.X n)
  have hΓ := isLE_sections_of_injective J a b hb hi hqc
  let F := ModuleCat.restrictScalars (algebraMap R (Localization.Away r))
  have hF : CochainComplex.IsLE ((F.mapHomologicalComplex (.up ℤ)).obj
      ((sectionsComplex (CommRingCat.of (Localization.Away r))).obj J)) b := by
    rw [CochainComplex.isLE_iff]
    intro n hn
    exact (((sectionsComplex (CommRingCat.of (Localization.Away r))).obj J).exactAt_of_isLE b n
      hn).map F
  rw [CochainComplex.isLE_iff]
  intro n hn
  exact (CochainComplex.exactAt_of_isLE
    ((F.mapHomologicalComplex (.up ℤ)).obj
      ((sectionsComplex (CommRingCat.of (Localization.Away r))).obj J)) b n hn).of_iso
    ((NatIso.mapHomologicalComplex (principalRestrictionSectionsIso R r) (.up ℤ)).app I)

/-- Quasicoherent homology on an arbitrary open survives restriction to each
contained principal chart, without any cohomological bound. -/
lemma principalRestriction_quasicoherent_of_open {R : CommRingCat.{u}}
    (I : CochainComplex (Spec R).Modules ℤ) (W : (Spec R).Opens)
    (hqc : ∀ n, (((restrict W.ι).obj I).homology n).IsQuasicoherent)
    (r : R) (hr : PrimeSpectrum.basicOpen r ≤ W) (n : ℤ) :
    (((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj I).homology
      n).IsQuasicoherent := by
  let j := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r
  have hjW : Set.range j ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange,
      Scheme.Hom.opensRange_localizationAway r]
    exact hr
  let k := IsOpenImmersion.lift W.ι j hjW
  have hk : k ≫ W.ι = j := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (k ≫ W.ι) := by rw [hk]; infer_instance
  have : IsOpenImmersion k := IsOpenImmersion.of_comp k W.ι
  let e : (restrict k).obj ((restrict W.ι).obj I) ≅ (restrict j).obj I :=
    (restrictCompIso k W.ι ≪≫ eqToIso (restrict_congr hk)).app I
  exact (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of (Localization.Away
    r))).ringCatSheaf).prop_of_iso
    ((homologyFunctor (Spec (CommRingCat.of (Localization.Away r))).Modules (.up ℤ) n).mapIso e)
    (quasicoherent_homology_restrict k ((restrict W.ι).obj I) hqc n)

/-- On every principal contained in W, the actual restricted complex inherits
both its homology bound and quasicoherence from the original restriction to W. -/
lemma principalRestriction_bounds_of_open {R : CommRingCat.{u}}
    (I : CochainComplex (Spec R).Modules ℤ) (W : (Spec R).Opens) (b : ℤ)
    [((restrict W.ι).obj I).IsLE b]
    (hqc : ∀ n, (((restrict W.ι).obj I).homology n).IsQuasicoherent)
    (r : R) (hr : PrimeSpectrum.basicOpen r ≤ W) :
    ((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj I).IsLE b ∧
      (∀ n, (((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj
        I).homology n).IsQuasicoherent) :=
        by
  let j := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r
  have hjW : Set.range j ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange,
      Scheme.Hom.opensRange_localizationAway r]
    exact hr
  let k := IsOpenImmersion.lift W.ι j hjW
  have hk : k ≫ W.ι = j := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (k ≫ W.ι) := by rw [hk]; infer_instance
  have : IsOpenImmersion k := IsOpenImmersion.of_comp k W.ι
  let e : (restrict k).obj ((restrict W.ι).obj I) ≅ (restrict j).obj I :=
    (restrictCompIso k W.ι ≪≫ eqToIso (restrict_congr hk)).app I
  have hbound : ((restrict k).obj ((restrict W.ι).obj I)).IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro n hn
    exact (((restrict W.ι).obj I).exactAt_of_isLE b n hn).map (Scheme.Modules.restrictFunctor k)
  refine ⟨CochainComplex.isLE_of_iso e b, fun n => ?_⟩
  exact (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of (Localization.Away
    r))).ringCatSheaf).prop_of_iso
    ((homologyFunctor (Spec (CommRingCat.of (Localization.Away r))).Modules (.up ℤ) n).mapIso e)
    (quasicoherent_homology_restrict k ((restrict W.ι).obj I) hqc n)

/-- Genuine finite-principal geometric upper bound for an original injective
complex. Quasicoherence and the upper bound are required only after restricting
to W; no principal-section acyclicity premise remains. -/
lemma isLE_sections_finitePrincipal_of_injective {R : CommRingCat.{u}}
    (I : CochainComplex (Spec R).Modules ℤ) (a b : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (W : (Spec R).Opens) [((restrict W.ι).obj I).IsLE b]
    (hqc : ∀ n, (((restrict W.ι).obj I).homology n).IsQuasicoherent)
    (s : Finset R) (hs : SheafCohomology.principalUnion R s ≤ W) :
    CochainComplex.IsLE (((affineSectionsAt R (SheafCohomology.principalUnion R
      s)).mapHomologicalComplex
      (.up ℤ)).obj I) (b + (s.card : ℤ) - 1) := by
  let K := ((modulesSpecToSheaf (R := R)).mapHomologicalComplex (.up ℤ)).obj I
  have hf (n : ℤ) : TopCat.Presheaf.IsFlasque (K.X n).obj := by
    let := hinj n
    let := AlgebraicGeometry.Scheme.Modules.injective_isFlasque (Spec R) (I.X n)
    exact isFlasque_modulesSpecToSheaf (I.X n)
  apply SheafCohomology.sectionsComplex_isLE_principalUnion R K W b ?_ s hs
  intro r hr
  obtain ⟨hb, hq⟩ := principalRestriction_bounds_of_open I W b hqc r hr
  exact isLE_principalSections_of_injective I a b hbound hinj r hq

/-- Actual R-module sections on a compact open are cohomologically bounded
above when the original restricted injective complex has bounded QC homology. -/
lemma exists_isLE_sections_compactOpen_of_injective {R : CommRingCat.{u}}
    (I : CochainComplex (Spec R).Modules ℤ) (a b : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    [((restrict W.ι).obj I).IsLE b]
    (hqc : ∀ n, (((restrict W.ι).obj I).homology n).IsQuasicoherent) :
    ∃ n : ℤ, CochainComplex.IsLE
      (((affineSectionsAt R W).mapHomologicalComplex (.up ℤ)).obj I) n := by
  let K := ((modulesSpecToSheaf (R := R)).mapHomologicalComplex (.up ℤ)).obj I
  have hf (n : ℤ) : TopCat.Presheaf.IsFlasque (K.X n).obj := by
    let := hinj n
    let := AlgebraicGeometry.Scheme.Modules.injective_isFlasque (Spec R) (I.X n)
    exact isFlasque_modulesSpecToSheaf (I.X n)
  apply SheafCohomology.exists_sectionsComplex_isLE_of_isCompact R K W hW b
  intro r hr
  obtain ⟨hb, hq⟩ := principalRestriction_bounds_of_open I W b hqc r hr
  exact isLE_principalSections_of_injective I a b hbound hinj r hq

/-- The original ambient injective model of a bounded QC complex on a compact
open can be chosen with genuinely bounded R-module sections on that open.
This retains the original weak map into its restriction and the exact lower
term bound; it does not yet assert an associated-sheaf comparison on the open. -/
lemma exists_open_injective_model_with_bounded_sections (R : CommRingCat.{u})
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (E : CochainComplex W.toScheme.Modules ℤ) (a b : ℤ) [E.IsGE a] [E.IsLE b]
    (hqc : ∀ n, (E.homology n).IsQuasicoherent) :
    ∃ (I : CochainComplex (Spec R).Modules ℤ) (q : E ⟶ (restrict W.ι).obj I) (c : ℤ),
      I.IsStrictlyGE a ∧ (∀ n, Injective (I.X n)) ∧ QuasiIso q ∧
      CochainComplex.IsStrictlyGE
        (((affineSectionsAt R W).mapHomologicalComplex (.up ℤ)).obj I) a ∧
      CochainComplex.IsLE
        (((affineSectionsAt R W).mapHomologicalComplex (.up ℤ)).obj I) c := by
  obtain ⟨I, q, hIa, hI, hq⟩ := exists_open_injective_quasiIso W.ι E a
  let := hIa
  let := hq
  have hqcI (n : ℤ) : (((restrict W.ι).obj I).homology n).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso
      (isoOfQuasiIsoAt q n) (hqc n)
  have hb : ((restrict W.ι).obj I).IsLE b := by
    rw [CochainComplex.isLE_iff]
    intro n hn
    exact (exactAt_iff_of_quasiIsoAt q n).mp (E.exactAt_of_isLE b n hn)
  obtain ⟨c, hc⟩ := exists_isLE_sections_compactOpen_of_injective I a b
    (fun n hn => I.isZero_of_isStrictlyGE a n hn) hI W hW hqcI
  refine ⟨I, q, c, hIa, hI, hq, ?_, hc⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  exact (affineSectionsAt R W).map_isZero (I.isZero_of_isStrictlyGE a n hn)

end Quillen.PerfectComplexes.Affine
