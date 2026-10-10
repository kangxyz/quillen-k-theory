/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenSectionsBounds

/-! Original-map and endpoint consumers of geometric finite-open section bounds. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
  Opposite
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
namespace Quillen.Tests.OpenSectionsBounds

/-- The actual affine sections have vanishing homology above the original
sheaf-cohomology bound; no upper bound on the injective terms is used. -/
lemma actual_affine_homology_vanishes {R : CommRingCat.{u}}
    (I : Complex (Spec R)) (a b : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (I.homology n).IsQuasicoherent) [I.IsLE b] (n : ℤ) (hn : b < n) :
    IsZero (((sectionsComplex R).obj I).homology n) := by
  have := isLE_sections_of_injective I a b hbound hinj hqc
  exact CochainComplex.isZero_of_isLE _ b n hn

/-- Exact cohomology vanishing degree for an arbitrary original finite family. -/
lemma finite_union_homology_vanishes {R : CommRingCat.{u}}
    (I : Complex (Spec R)) (a b : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (W : (Spec R).Opens) [((restrict W.ι).obj I).IsLE b]
    (hqc : ∀ n, (((restrict W.ι).obj I).homology n).IsQuasicoherent)
    (s : Finset R) (hs : SheafCohomology.principalUnion R s ≤ W)
    (n : ℤ) (hn : b + (s.card : ℤ) - 1 < n) :
    IsZero ((((affineSectionsAt R (SheafCohomology.principalUnion R s)).mapHomologicalComplex
      (.up ℤ)).obj I).homology n) := by
  have := isLE_sections_finitePrincipal_of_injective I a b hbound hinj W hqc s hs
  exact CochainComplex.isZero_of_isLE _ (b + (s.card : ℤ) - 1) n hn

/-- The genuine compact-open result only uses QC on the chosen restriction. -/
lemma compact_open_homology_bound {R : CommRingCat.{u}}
    (I : Complex (Spec R)) (a b : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    [((restrict W.ι).obj I).IsLE b]
    (hqc : ∀ n, (((restrict W.ι).obj I).homology n).IsQuasicoherent) :
    ∃ c : ℤ, ∀ n : ℤ, c < n → IsZero
      ((((affineSectionsAt R W).mapHomologicalComplex (.up ℤ)).obj I).homology n) := by
  obtain ⟨c, hc⟩ := exists_isLE_sections_compactOpen_of_injective I a b hbound hinj W hW hqc
  exact ⟨c, fun n hn => CochainComplex.isZero_of_isLE _ c n hn⟩

/-- The model retains the original homology maps and exact lower term bound
on actual R-module sections. -/
lemma original_model_homology_maps (R : CommRingCat.{u}) (W : (Spec R).Opens)
    (hW : IsCompact (W : Set (Spec R))) (E : Complex W.toScheme)
    (a b : ℤ) [E.IsGE a] [E.IsLE b]
    (hqc : ∀ n, (E.homology n).IsQuasicoherent) :
    ∃ (I : Complex (Spec R)) (q : E ⟶ (restrict W.ι).obj I) (c : ℤ),
      (∀ n, IsIso (homologyMap q n)) ∧
      (∀ n, n < a → IsZero (((affineSectionsAt R W).mapHomologicalComplex (.up ℤ)).obj I |>.X n)) ∧
      (∀ n, c < n → IsZero ((((affineSectionsAt R W).mapHomologicalComplex (.up ℤ)).obj I).homology
        n)) := by
  obtain ⟨I, q, c, hI, hi, hq, hPa, hPc⟩ :=
    exists_open_injective_model_with_bounded_sections R W hW E a b hqc
  let := hq
  let := hPa
  let := hPc
  exact ⟨I, q, c, fun n => inferInstance,
    fun n hn => CochainComplex.isZero_of_isStrictlyGE _ a n hn,
    fun n hn => CochainComplex.isZero_of_isLE _ c n hn⟩

/-- Localization at zero is allowed in the genuine principal-section bound. -/
lemma zero_principal_homology_bound {R : CommRingCat.{u}}
    (I : Complex (Spec R)) (a b : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (((restrict (CoherentScheme.principalOpen R 0)).obj I).homology n).IsQuasicoherent)
    [((restrict (CoherentScheme.principalOpen R 0)).obj I).IsLE b] :
    CochainComplex.IsLE (((affineSectionsAt R (PrimeSpectrum.basicOpen (0 :
      R))).mapHomologicalComplex
      (.up ℤ)).obj I) b :=
  isLE_principalSections_of_injective I a b hbound hinj 0 hqc

end Quillen.Tests.OpenSectionsBounds
