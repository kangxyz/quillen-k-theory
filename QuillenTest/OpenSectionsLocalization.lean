/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenSectionsLocalization

/-! # Actual pullback and compact-open localization consumers -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
open Quillen.PerfectComplexes Quillen.PerfectComplexes.Affine
namespace QuillenTest.OpenSectionsLocalization

open Quillen

/-- The actual pullback corner map, with every original commuting square retained. -/
theorem original_pullback_corner {C : Type u} [Category.{v} C] [Abelian C]
    {P X Y Z P' X' Y' Z' : CochainComplex C ℤ}
    {i : P ⟶ X} {j : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    {i' : P' ⟶ X'} {j' : P' ⟶ Y'} {f' : X' ⟶ Z'} {g' : Y' ⟶ Z'}
    [Epi f] [Epi f'] (h : IsPullback i j f g) (h' : IsPullback i' j' f' g')
    (a : P ⟶ P') (b : X ⟶ X') (c : Y ⟶ Y') (d : Z ⟶ Z')
    (hi : i ≫ b = a ≫ i') (hj : j ≫ c = a ≫ j')
    (hf : f ≫ d = b ≫ f') (hg : g ≫ d = c ≫ g')
    [QuasiIso b] [QuasiIso c] [QuasiIso d] (n : ℤ) :
    QuasiIso a ∧ IsIso (homologyMap a n) := by
  have ha := Quillen.CochainComplex.quasiIso_pullback_gluing h h' a b c d hi hj hf hg
  exact ⟨ha, inferInstance⟩

/-- No injectivity, lower bound, or quasicoherence is needed for the original empty-open map. -/
theorem original_empty_open (R : CommRingCat.{u}) (r : R) (I : Complex (Spec R)) :
    IsIso (sectionsLocalizationComplexComparison R r ⊥ I) :=
  isIso_sectionsLocalizationComplexComparison_bot R r I

/-- The original compact-open restriction factors through its now-proved weak localization map. -/
theorem original_compact_map_and_numerator (R : CommRingCat.{u}) (r : R)
    (I : Complex (Spec R)) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (hqc : ∀ n, (((restrict W.ι).obj I).homology n).IsQuasicoherent) :
    QuasiIso (sectionsLocalizationComplexComparison R r W I) ∧
    (NatTrans.mapHomologicalComplex (scalarLocalizeUnit R r) (.up ℤ)).app
        (affineSectionsComplex R W I) ≫ sectionsLocalizationComplexComparison R r W I =
      affineSectionsComplexRestriction R (inf_le_left : W ⊓ PrimeSpectrum.basicOpen r ≤ W) I :=
  ⟨quasiIso_sectionsLocalizationComplexComparison_of_quasicoherent_on_open r I a hbound hinj W hW
    hqc,
    sectionsLocalizationComplexComparison_unit R r W I⟩

/-- The finite family need not cover the ambient spectrum, and QC is required only on W. -/
theorem original_partial_principal_family (R : CommRingCat.{u}) (r : R)
    (I : Complex (Spec R)) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (W : (Spec R).Opens)
    (hqc : ∀ n, (((restrict W.ι).obj I).homology n).IsQuasicoherent)
    (s : Finset R) (hs : Quillen.SheafCohomology.principalUnion R s ≤ W) :
    QuasiIso (sectionsLocalizationComplexComparison R r (Quillen.SheafCohomology.principalUnion R s)
      I) := by
  apply quasiIso_sectionsLocalizationComplexComparison_principalUnion r I hinj W _ s hs
  intro q hq
  exact quasiIso_sectionsLocalizationComplexComparison_basicOpen r q I a hbound hinj
    (principalRestriction_quasicoherent_of_open I W hqc q hq)

/-- Both original homology inverse laws hold at every degree with no upper bound. -/
theorem original_compact_homology_inverse (R : CommRingCat.{u}) (r : R)
    (I : Complex (Spec R)) (a n : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (hqc : ∀ n, (((restrict W.ι).obj I).homology n).IsQuasicoherent) :
    ∃ p, homologyMap (sectionsLocalizationComplexComparison R r W I) n ≫ p = 𝟙 _ ∧
      p ≫ homologyMap (sectionsLocalizationComplexComparison R r W I) n = 𝟙 _ := by
  let := quasiIso_sectionsLocalizationComplexComparison_of_quasicoherent_on_open r I a hbound hinj W
    hW hqc
  exact ⟨inv _, IsIso.hom_inv_id _, IsIso.inv_hom_id _⟩

end QuillenTest.OpenSectionsLocalization
