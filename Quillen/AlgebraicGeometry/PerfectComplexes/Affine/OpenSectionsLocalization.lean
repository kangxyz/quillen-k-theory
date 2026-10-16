/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionsLocalizationQuasiIso
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenSectionsBounds
public import Quillen.Waldhausen.Duality.PullbackGluing

/-!
# Original localization of sections on a compact open

For an actual lower-bounded complex of injective all-module sheaves on an
affine scheme, the original map Gamma(W)[1/r] to Gamma(W intersect D(r)) is
a quasi-isomorphism whenever W is compact and homology is quasicoherent on W.
There is no ambient quasicoherence or upper cohomological bound assumption.

Actual section squares are pullbacks, and injective terms make their legs
epic. Exact scalar localization and genuine pullback gluing prove binary
union closure of the original comparison. A finite principal-cover induction
then uses the proved principal-local leaf. Empty opens and empty families
are included. The endpoint retains the original localization numerator and
strict shrinking-open square from SectionsLocalization.
-/
@[expose] public section

open HomologicalComplex
open Quillen.SheafCohomology


open AlgebraicGeometry.Scheme.Modules.Complex


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
  HomologicalComplex

namespace Quillen.PerfectComplexes.Affine

local instance modulesSpecToSheaf_additive (R : CommRingCat.{u}) :
    (modulesSpecToSheaf (R := R)).Additive where
  map_add := by intros; rfl

/-- The original affine module-sheaf complex with its constant R-module coefficients. -/
abbrev affineUnderlyingSheafComplex (R : CommRingCat.{u}) (I : CochainComplex (Spec R).Modules ℤ) :=
  (modulesSpecToSheaf (R := R)).mapHomologicalComplex (.up ℤ) |>.obj I

/-- Actual section squares remain pullbacks with any equal choices of their union and intersection.
-/
lemma affineSectionsComplex_isPullback (R : CommRingCat.{u}) (I : CochainComplex (Spec R).Modules ℤ)
    {U V W T : (Spec R).Opens} (hW : U ⊔ V = W) (hT : U ⊓ V = T)
    (hU : U ≤ W) (hV : V ≤ W) (hTU : T ≤ U) (hTV : T ≤ V) :
    IsPullback (affineSectionsComplexRestriction R hU I) (affineSectionsComplexRestriction R hV I)
      (affineSectionsComplexRestriction R hTU I) (affineSectionsComplexRestriction R hTV I) := by
  subst W
  subst T
  exact TopCat.Sheaf.sectionsComplex_isPullback (affineUnderlyingSheafComplex R I) U V

/-- Injective sheaf terms give actual epic section restriction chain maps. -/
lemma epi_affineSectionsComplexRestriction (R : CommRingCat.{u})
    (I : CochainComplex (Spec R).Modules ℤ)
    (hinj : ∀ n, Injective (I.X n)) {U V : (Spec R).Opens} (h : U ≤ V) :
    Epi (affineSectionsComplexRestriction R h I) := by
  apply HomologicalComplex.epi_of_epi_f
  intro n
  let := hinj n
  change Epi ((modulesSpecToSheaf.obj (I.X n)).obj.map (homOfLE h).op)
  rw [ModuleCat.epi_iff_surjective]
  exact AlgebraicGeometry.Scheme.Modules.injective_sections_restrict_surjective (Spec R) (I.X n)
    (homOfLE h)

/-- The original localized comparison is weak on a union if it is weak on both opens
and their actual intersection. This is genuine pullback gluing of section complexes. -/
lemma quasiIso_sectionsLocalizationComplexComparison_sup {R : CommRingCat.{u}} (r : R)
    (I : CochainComplex (Spec R).Modules ℤ) (hinj : ∀ n, Injective (I.X n)) (U V : (Spec R).Opens)
    [QuasiIso (sectionsLocalizationComplexComparison R r U I)]
    [QuasiIso (sectionsLocalizationComplexComparison R r V I)]
    [QuasiIso (sectionsLocalizationComplexComparison R r (U ⊓ V) I)] :
    QuasiIso (sectionsLocalizationComplexComparison R r (U ⊔ V) I) := by
  let F := (scalarLocalize R r).mapHomologicalComplex (.up ℤ)
  have h := affineSectionsComplex_isPullback R I (U := U) (V := V) rfl rfl
    le_sup_left le_sup_right inf_le_left inf_le_right
  have h' := affineSectionsComplex_isPullback R I
    (U := U ⊓ PrimeSpectrum.basicOpen r) (V := V ⊓ PrimeSpectrum.basicOpen r)
    (W := (U ⊔ V) ⊓ PrimeSpectrum.basicOpen r) (T := (U ⊓ V) ⊓ PrimeSpectrum.basicOpen r)
    (by
      apply SetLike.ext
      intro x
      change (x ∈ U ∧ x ∈ PrimeSpectrum.basicOpen r) ∨ (x ∈ V ∧ x ∈ PrimeSpectrum.basicOpen r) ↔
        (x ∈ U ∨ x ∈ V) ∧ x ∈ PrimeSpectrum.basicOpen r
      tauto) (by ac_rfl)
    (inf_le_inf le_sup_left le_rfl) (inf_le_inf le_sup_right le_rfl)
    (inf_le_inf inf_le_left le_rfl) (inf_le_inf inf_le_right le_rfl)
  have := epi_affineSectionsComplexRestriction R I hinj (inf_le_left : U ⊓ V ≤ U)
  have := epi_affineSectionsComplexRestriction R I hinj
    (inf_le_inf inf_le_left le_rfl : (U ⊓ V) ⊓ PrimeSpectrum.basicOpen r ≤ U ⊓
      PrimeSpectrum.basicOpen r)
  exact Quillen.CochainComplex.quasiIso_pullback_gluing (h.map F) h'
    (sectionsLocalizationComplexComparison R r (U ⊔ V) I)
    (sectionsLocalizationComplexComparison R r U I)
    (sectionsLocalizationComplexComparison R r V I)
    (sectionsLocalizationComplexComparison R r (U ⊓ V) I)
    (sectionsLocalizationComplexComparison_restrict R r le_sup_left I)
    (sectionsLocalizationComplexComparison_restrict R r le_sup_right I)
    (sectionsLocalizationComplexComparison_restrict R r inf_le_left I)
    (sectionsLocalizationComplexComparison_restrict R r inf_le_right I)


/-- Empty-open localization is an actual isomorphism between zero complexes. -/
lemma isIso_sectionsLocalizationComplexComparison_bot (R : CommRingCat.{u}) (r : R)
    (I : CochainComplex (Spec R).Modules ℤ) : IsIso
      (sectionsLocalizationComplexComparison R r ⊥ I) := by
  have h0 : IsZero (affineSectionsComplex R ⊥ I) :=
    isZero_sectionsComplex_bot (affineUnderlyingSheafComplex R I)
  have ht : IsZero (affineSectionsComplex R (⊥ ⊓ PrimeSpectrum.basicOpen r) I) := by
    simpa only [bot_inf_eq] using h0
  exact (((scalarLocalize R r).mapHomologicalComplex (.up ℤ)).map_isZero h0).isIso ht _

/-- Genuine finite-union induction for the literal localization comparison.
Every principal leaf premise is about the same original map. -/
lemma quasiIso_sectionsLocalizationComplexComparison_principalUnion {R : CommRingCat.{u}} (r : R)
    (I : CochainComplex (Spec R).Modules ℤ) (hinj : ∀ n, Injective (I.X n)) (W : (Spec R).Opens)
    (hlocal : ∀ q : R, PrimeSpectrum.basicOpen q ≤ W →
      QuasiIso (sectionsLocalizationComplexComparison R r (PrimeSpectrum.basicOpen q) I))
    (s : Finset R) (hs : principalUnion R s ≤ W) :
    QuasiIso (sectionsLocalizationComplexComparison R r (principalUnion R s) I) := by
  classical
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases hz : s = ∅
    · subst s
      erw [principalUnion_empty R]
      let := isIso_sectionsLocalizationComplexComparison_bot R r I
      infer_instance
    obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hz
    let t := s.erase q
    have hqt : insert q t = s := Finset.insert_erase hq
    have hcard : t.card + 1 = s.card := Finset.card_erase_add_one hq
    have ht : principalUnion R t ≤ W :=
      (principalUnion_mono R (Finset.erase_subset q s)).trans hs
    have hi : principalUnion R (t.image (fun z => z * q)) ≤ W := by
      erw [principalUnion_mul R]
      exact inf_le_left.trans ht
    have hct : t.card < n := by omega
    have hci : (t.image (fun z => z * q)).card < n :=
      lt_of_le_of_lt Finset.card_image_le hct
    have htweak := ih t.card hct t ht rfl
    have hiweak := ih _ hci (t.image (fun z => z * q)) hi rfl
    have hqweak := hlocal q ((basicOpen_le_principalUnion R hq).trans hs)
    have : QuasiIso (sectionsLocalizationComplexComparison R r
        (PrimeSpectrum.basicOpen q ⊓ principalUnion R t) I) := by
      erw [inf_comm, ← principalUnion_mul R]
      exact hiweak
    have hout := quasiIso_sectionsLocalizationComplexComparison_sup r I hinj
      (PrimeSpectrum.basicOpen q) (principalUnion R t)
    erw [← principalUnion_insert R, hqt] at hout
    exact hout

/-- A genuine finite principal cover extends original localization weakness to the compact open. -/
lemma quasiIso_sectionsLocalizationComplexComparison_of_isCompact {R : CommRingCat.{u}} (r : R)
    (I : CochainComplex (Spec R).Modules ℤ) (hinj : ∀ n, Injective (I.X n)) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R)))
    (hlocal : ∀ q : R, PrimeSpectrum.basicOpen q ≤ W →
      QuasiIso (sectionsLocalizationComplexComparison R r (PrimeSpectrum.basicOpen q) I)) :
    QuasiIso (sectionsLocalizationComplexComparison R r W I) := by
  classical
  obtain ⟨ι, _, q, hq⟩ := PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact W hW
  let := Fintype.ofFinite ι
  let s : Finset R := Finset.univ.image q
  have hs : principalUnion R s = W := by
    rw [hq]
    apply le_antisymm
    · refine iSup₂_le fun z hz => ?_
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
      exact le_iSup (fun i => PrimeSpectrum.basicOpen (q i)) i
    · exact iSup_le fun i => basicOpen_le_principalUnion R
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  rw [← hs]
  exact quasiIso_sectionsLocalizationComplexComparison_principalUnion r I hinj W hlocal s hs.le

/-- Genuine compact-open section localization for an actual lower-bounded injective complex.
Quasicoherent homology is required only on the selected open. -/
lemma quasiIso_sectionsLocalizationComplexComparison_of_quasicoherent_on_open
    {R : CommRingCat.{u}} (r : R) (I : CochainComplex (Spec R).Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (hqc : ∀ n, (((restrict W.ι).obj I).homology n).IsQuasicoherent) :
    QuasiIso (sectionsLocalizationComplexComparison R r W I) := by
  apply quasiIso_sectionsLocalizationComplexComparison_of_isCompact r I hinj W hW
  intro q hq
  exact quasiIso_sectionsLocalizationComplexComparison_basicOpen r q I a hbound hinj
    (principalRestriction_quasicoherent_of_open I W hqc q hq)

end Quillen.PerfectComplexes.Affine
