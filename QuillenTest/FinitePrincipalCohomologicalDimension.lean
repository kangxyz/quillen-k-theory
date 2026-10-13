/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.FinitePrincipalCohomologicalDimension
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Data.ZMod.Basic

/-! Semantic consumers of the original Mayer--Vietoris maps and finite
principal-cover bounds, including empty opens and zero divisors. -/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open Quillen.SheafCohomology
namespace QuillenTest.FinitePrincipalCohomologicalDimension

open Quillen

variable {X : TopCat.{u}} {A : Type v} [Category.{u} A] [Abelian A]
  [HasSheafify (Opens.grothendieckTopology X) A]

/-- Both differentials retain the actual restrictions, including the sign. -/
lemma original_differentials (K : CochainComplex (TopCat.Sheaf A X) ℤ) (U V : Opens X) :
    (sectionsMayerVietoris K U V).f =
      biprod.lift (sectionsComplexRestriction K le_sup_left)
        (sectionsComplexRestriction K le_sup_right) ∧
    (sectionsMayerVietoris K U V).g =
      biprod.desc (sectionsComplexRestriction K inf_le_left)
        (-sectionsComplexRestriction K inf_le_right) := ⟨rfl, rfl⟩

/-- Shrinking opens uses the same original restriction in every position. -/
lemma original_restriction_components (K : CochainComplex (TopCat.Sheaf A X) ℤ)
    {U V U' V' : Opens X} (hU : U' ≤ U) (hV : V' ≤ V) :
    (sectionsMayerVietorisRestriction K hU hV).τ₁ =
      sectionsComplexRestriction K (sup_le_sup hU hV) ∧
    (sectionsMayerVietorisRestriction K hU hV).τ₂ =
      biprod.map (sectionsComplexRestriction K hU) (sectionsComplexRestriction K hV) ∧
    (sectionsMayerVietorisRestriction K hU hV).τ₃ =
      sectionsComplexRestriction K (inf_le_inf hU hV) := ⟨rfl, rfl, rfl⟩

/-- The original section difference is an epimorphism of complexes. -/
lemma original_difference_epi (K : CochainComplex (TopCat.Sheaf A X) ℤ)
    [∀ i, TopCat.Presheaf.IsFlasque (K.X i).obj] (U V : Opens X) :
    Epi (biprod.desc (sectionsComplexRestriction K (inf_le_left : U ⊓ V ≤ U))
      (-sectionsComplexRestriction K (inf_le_right : U ⊓ V ≤ V))) :=
  (sectionsMayerVietoris_shortExact K U V).epi_g

/-- The sharp intersection endpoint is one degree below the union bound. -/
lemma sharp_union_bound (K : CochainComplex (TopCat.Sheaf A X) ℤ)
    [∀ i, TopCat.Presheaf.IsFlasque (K.X i).obj] (U V : Opens X) (b : ℤ)
    [CochainComplex.IsLE (sectionsComplex K U) b]
    [CochainComplex.IsLE (sectionsComplex K V) b]
    [CochainComplex.IsLE (sectionsComplex K (U ⊓ V)) (b - 1)] :
    CochainComplex.IsLE (sectionsComplex K (U ⊔ V)) b :=
  sectionsComplex_isLE_sup K U V b

/-- Empty-open sections vanish without any termwise flasque assumption. -/
lemma empty_complex_original_identity (K : CochainComplex (TopCat.Sheaf A X) ℤ) :
    𝟙 (sectionsComplex K ⊥) = 0 :=
  (isZero_sectionsComplex_bot K).eq_of_src _ _

variable (R : CommRingCat.{u})
  [HasSheafify (Opens.grothendieckTopology (TopCat.of (PrimeSpectrum R))) A]
  (K : CochainComplex (TopCat.Sheaf A (TopCat.of (PrimeSpectrum R))) ℤ)
  [∀ i, TopCat.Presheaf.IsFlasque (K.X i).obj]

lemma original_finite_bound (W : Opens (PrimeSpectrum R)) (b : ℤ)
    (hlocal : ∀ r : R, PrimeSpectrum.basicOpen r ≤ W →
      CochainComplex.IsLE (sectionsComplex K (PrimeSpectrum.basicOpen r)) b)
    (s : Finset R) (hs : principalUnion R s ≤ W) :
    CochainComplex.IsLE (sectionsComplex K (⨆ r ∈ s, PrimeSpectrum.basicOpen r))
      (b + (s.card : ℤ) - 1) :=
  sectionsComplex_isLE_principalUnion R K W b hlocal s hs

lemma actual_compact_open_bound (W : Opens (PrimeSpectrum R))
    (hW : IsCompact (W : Set (PrimeSpectrum R))) (b : ℤ)
    (hlocal : ∀ r : R, PrimeSpectrum.basicOpen r ≤ W →
      CochainComplex.IsLE (sectionsComplex K (PrimeSpectrum.basicOpen r)) b) :
    ∃ n : ℤ, CochainComplex.IsLE (sectionsComplex K W) n :=
  exists_sectionsComplex_isLE_of_isCompact R K W hW b hlocal

local instance : DecidableEq (CommRingCat.of (ZMod 6)) := Classical.decEq _

/-- The finite family can contain a zero divisor and an empty principal open. -/
lemma zero_divisor_and_empty_open
    (K : CochainComplex (TopCat.Sheaf (ModuleCat.{0} (ZMod 6))
      (TopCat.of (PrimeSpectrum (ZMod 6)))) ℤ)
    [∀ i, TopCat.Presheaf.IsFlasque (K.X i).obj] (b : ℤ)
    (hlocal : ∀ r : ZMod 6,
      PrimeSpectrum.basicOpen r ≤ principalUnion (CommRingCat.of (ZMod 6)) {2, 0} →
      CochainComplex.IsLE (sectionsComplex K (PrimeSpectrum.basicOpen r)) b) :
    CochainComplex.IsLE
      (sectionsComplex K (PrimeSpectrum.basicOpen (2 : ZMod 6) ⊔
        PrimeSpectrum.basicOpen (0 : ZMod 6))) (b + 1) := by
  have h := sectionsComplex_isLE_principalUnion (CommRingCat.of (ZMod 6)) K
    (principalUnion (CommRingCat.of (ZMod 6)) {2, 0}) b hlocal {2, 0} le_rfl
  have hU : principalUnion (CommRingCat.of (ZMod 6)) {2, 0} =
      PrimeSpectrum.basicOpen (2 : ZMod 6) ⊔ PrimeSpectrum.basicOpen (0 : ZMod 6) := by
    classical
    rw [principalUnion_insert]
    congr 1
    simp only [principalUnion, Finset.mem_singleton, iSup_iSup_eq_left]
  rw [hU] at h
  have hc : ({2, 0} : Finset (CommRingCat.of (ZMod 6))).card ≤ 2 :=
    (Finset.card_insert_le _ _).trans (by simp)
  exact CochainComplex.isLE_of_le _ (b + (({2, 0} : Finset (CommRingCat.of (ZMod 6))).card : ℤ) - 1)
    (b + 1) (by omega)

end QuillenTest.FinitePrincipalCohomologicalDimension
