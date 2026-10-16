/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Homology
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.Affine.SectionsLocalization
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSections

public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction
/-!
# The original localized-section comparison on every principal chart

For a lower-bounded injective all-sheaf complex, the genuine comparison
`Γ(D(q), I)[1/r] → Γ(D(q) ∩ D(r), I)` is a quasi-isomorphism when the original
restricted complex on `D(q)` has quasicoherent homology. There is no upper
bound, no quasicoherence of the terms, and no ambient quasicoherence premise.

The map is exactly `sectionsLocalizationComplexComparison`, defined by the
localization universal property and original restriction of sections. The
proof transports actual right homology through affine restriction/global
sections, then applies ordinary denominator clearing to the actual homology
sheaf on that chart. General right-homology composition and natural-isomorphism
transport lemmas are proved as reusable intermediate steps.

Rings and localization elements are arbitrary, including zero divisors and
localization at zero. Finite-union propagation is a separate Mayer--Vietoris
argument using this affine-chart theorem as its geometric input.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

open AlgebraicGeometry.Scheme


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
  Opposite

namespace Quillen.SheafCohomology
variable {C : Type u} {D : Type v} {E : Type w}
  [Category.{u'} C] [Category.{v'} D] [Category.{w'} E]
  [Abelian C] [Abelian D] [Abelian E]

lemma preservesRightHomologyOf_comp (F : C ⥤ D) (G : D ⥤ E)
    [F.Additive] [G.Additive] [PreservesFiniteLimits F] [PreservesFiniteLimits G]
    (S : ShortComplex C) [F.PreservesRightHomologyOf S]
    [G.PreservesRightHomologyOf (S.map F)] : (F ⋙ G).PreservesRightHomologyOf S := by
  let h := S.homologyData.right
  let : PreservesColimit (parallelPair S.f 0) F :=
    ShortComplex.RightHomologyData.IsPreservedBy.hf h F
  let : PreservesColimit (parallelPair (F.map S.f) 0) G :=
    ShortComplex.RightHomologyData.IsPreservedBy.hf (S.map F).homologyData.right G
  let e : parallelPair S.f 0 ⋙ F ≅ parallelPair (F.map S.f) 0 :=
    diagramIsoParallelPair _ ≪≫ parallelPair.ext (Iso.refl _) (Iso.refl _)
      (by simp) (by simp)
  let : PreservesColimit (parallelPair S.f 0 ⋙ F) G :=
    preservesColimit_of_iso_diagram G e.symm
  let : h.IsPreservedBy (F ⋙ G) := { f := inferInstance, g' := inferInstance }
  exact Functor.PreservesRightHomologyOf.mk' _ h

lemma preservesRightHomologyOf_natIso {F G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ≅ G) (S : ShortComplex C) [F.PreservesRightHomologyOf S] :
    G.PreservesRightHomologyOf S := by
  refine ⟨fun h => ?_⟩
  let : PreservesColimit (parallelPair S.f 0) F :=
    ShortComplex.RightHomologyData.IsPreservedBy.hf h F
  let : PreservesLimit (parallelPair h.g' 0) F :=
    ShortComplex.RightHomologyData.IsPreservedBy.hg' h F
  exact ⟨preservesColimit_of_natIso _ e, preservesLimit_of_natIso _ e⟩
end Quillen.SheafCohomology

namespace Quillen.PerfectComplexes.Affine
local instance principalSectionsHomologyGlobalSections_isRightAdjoint (R : CommRingCat.{u}) (r : R)
  :
    (moduleSpecΓFunctor (R := CommRingCat.of (Localization.Away r))).IsRightAdjoint :=
  tilde.adjunction.isRightAdjoint

local instance principalSectionsHomologyGlobalSections_additive (R : CommRingCat.{u}) (r : R) :
    (moduleSpecΓFunctor (R := CommRingCat.of (Localization.Away r))).Additive :=
  AlgebraicGeometry.Scheme.Modules.moduleSpecΓFunctor_additive _

lemma principalSections_preservesRightHomology {R : CommRingCat.{u}}
    (I : CochainComplex (Spec R).Modules ℤ) (a : ℤ) (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n)) (r : R)
    (hqc : ∀ n, (((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r)).obj
      I).homology n).IsQuasicoherent)
    (n : ℤ) : (affineSectionsAt R (PrimeSpectrum.basicOpen r)).PreservesRightHomologyOf (I.sc n) :=
      by
  let j := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R r
  let J := (restrict j).obj I
  have hb (n : ℤ) (hn : n < a) : IsZero (J.X n) :=
    (Scheme.Modules.restrictFunctor j).map_isZero (hbound n hn)
  have hi (n : ℤ) : Injective (J.X n) := by
    let := hinj n
    exact AlgebraicGeometry.Scheme.Modules.injective_restrict j (I.X n)
  let : (moduleSpecΓFunctor (R := CommRingCat.of (Localization.Away r))).PreservesRightHomologyOf
      ((I.sc n).map (Scheme.Modules.restrictFunctor j)) :=
    AlgebraicGeometry.Scheme.Modules.AffineCech.globalSections_preservesRightHomology J a hb hi hqc
      n
  let : (Scheme.Modules.restrictFunctor j ⋙ moduleSpecΓFunctor
      (R := CommRingCat.of (Localization.Away r))).PreservesRightHomologyOf (I.sc n) :=
    SheafCohomology.preservesRightHomologyOf_comp _ _ _
  let : ((Scheme.Modules.restrictFunctor j ⋙ moduleSpecΓFunctor
      (R := CommRingCat.of (Localization.Away r))) ⋙
        ModuleCat.restrictScalars (algebraMap R (Localization.Away r))).PreservesRightHomologyOf
          (I.sc n) :=
    SheafCohomology.preservesRightHomologyOf_comp _ _ _
  exact SheafCohomology.preservesRightHomologyOf_natIso (principalRestrictionSectionsIso R r) (I.sc
    n)

end Quillen.PerfectComplexes.Affine

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex TopologicalSpace
  Opposite
open scoped ModuleCat.Algebra
namespace Quillen.PerfectComplexes.Affine

/-- The generic localization lift is an actual isomorphism for sheaves that
are quasicoherent only after restriction to the chosen principal chart. -/
lemma isIso_sectionsLocalizationLift_basicOpen {R : CommRingCat.{u}} (r q : R)
    (M : (Spec R).Modules)
    [(M.restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R
      q)).IsQuasicoherent] :
    IsIso (sectionsLocalizationLift R r (PrimeSpectrum.basicOpen q) M) := by
  let g := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineSections.restriction M
    (PrimeSpectrum.basicOpen q) r
  let : IsLocalizedModule (Submonoid.powers r) g :=
    (Modules.QuasiCoherent.AffineSections.clearsDenominators_iff_isLocalized M
      (PrimeSpectrum.basicOpen q) r).mp
      (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.AffineSections.clearsDenominators_basicOpen M
        q r)
  let e := (IsLocalizedModule.linearEquiv (Submonoid.powers r)
    (scalarLocalizeMk R r ((affineSectionsAt R (PrimeSpectrum.basicOpen q)).obj M)) g).toModuleIso
  have he : sectionsLocalizationLift R r (PrimeSpectrum.basicOpen q) M = e.hom := by
    apply scalarLocalize_hom_ext R r (sectionsIntersection_units R r (PrimeSpectrum.basicOpen q) M)
    intro x
    simp only [Functor.comp_obj, evaluation_obj_obj]
    erw [sectionsLocalizationLift_mk]
  rw [he]
  infer_instance

/-- The literal original localized-section chain map is weak on every principal
chart. Its cohomology hypothesis is confined to that chart. -/
lemma quasiIso_sectionsLocalizationComplexComparison_basicOpen {R : CommRingCat.{u}}
    (r q : R) (I : CochainComplex (Spec R).Modules ℤ) (a : ℤ)
    (hbound : ∀ n, n < a → IsZero (I.X n)) (hinj : ∀ n, Injective (I.X n))
    (hqc : ∀ n, (((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R q)).obj
      I).homology n).IsQuasicoherent)
      :
    QuasiIso (sectionsLocalizationComplexComparison R r (PrimeSpectrum.basicOpen q) I) := by
  have hqcr (n : ℤ) :
      (((restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R (q * r))).obj
        I).homology n).IsQuasicoherent := by
    let j := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R q
    let k := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R (q * r)
    have hkj : Set.range k ⊆ Set.range j := by
      rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange,
        Scheme.Hom.opensRange_localizationAway, Scheme.Hom.opensRange_localizationAway]
      exact PrimeSpectrum.basicOpen_mul_le_left q r
    let l := IsOpenImmersion.lift j k hkj
    have hl : l ≫ j = k := IsOpenImmersion.lift_fac _ _ _
    have : IsOpenImmersion (l ≫ j) := by rw [hl]; infer_instance
    have : IsOpenImmersion l := IsOpenImmersion.of_comp l j
    let e : (restrict l).obj ((restrict j).obj I) ≅ (restrict k).obj I :=
      (restrictCompIso l j ≪≫ eqToIso (restrict_congr hl)).app I
    exact (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of (Localization.Away (q *
      r)))).ringCatSheaf).prop_of_iso
      ((homologyFunctor (Spec (CommRingCat.of (Localization.Away (q * r)))).Modules (.up ℤ)
        n).mapIso e)
      (quasicoherent_homology_restrict l ((restrict j).obj I) hqc n)
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let F := affineSectionsAt R (PrimeSpectrum.basicOpen q) ⋙ scalarLocalize R r
  let G := affineSectionsAt R (PrimeSpectrum.basicOpen q ⊓ PrimeSpectrum.basicOpen r)
  let : (affineSectionsAt R (PrimeSpectrum.basicOpen q)).PreservesRightHomologyOf (I.sc n) :=
    principalSections_preservesRightHomology I a hbound hinj q hqc n
  let : (moduleSpecΓFunctor (R := CommRingCat.of (Localization.Away q))).IsRightAdjoint :=
    tilde.adjunction.isRightAdjoint
  let : PreservesFiniteLimits (affineSectionsAt R (PrimeSpectrum.basicOpen q)) :=
    preservesFiniteLimits_of_natIso (principalRestrictionSectionsIso R q)
  let : F.PreservesRightHomologyOf (I.sc n) :=
    SheafCohomology.preservesRightHomologyOf_comp _ _ _
  let : (affineSectionsAt R (PrimeSpectrum.basicOpen (q * r))).PreservesRightHomologyOf (I.sc n) :=
    principalSections_preservesRightHomology I a hbound hinj (q * r) hqcr n
  let : G.PreservesRightHomologyOf (I.sc n) :=
    SheafCohomology.preservesRightHomologyOf_natIso
      (affineSectionsAtCongr R (PrimeSpectrum.basicOpen_mul q r)) (I.sc n)
  let h := (I.sc n).homologyData.right
  have hH : (h.H.restrict (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R
    q)).IsQuasicoherent := by
    have hIH : ((I.homology n).restrict
      (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R q)).IsQuasicoherent :=
      (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of (Localization.Away
        q))).ringCatSheaf).prop_of_iso
        (restrictHomologyIso (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen R q) I n)
          (hqc n)
    exact (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of (Localization.Away
      q))).ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctor (AlgebraicGeometry.Scheme.Modules.QuasiCoherent.principalOpen
        R q)).mapIso h.homologyIso) hIH
  let := isIso_sectionsLocalizationLift_basicOpen r q h.H
  let γ := ShortComplex.RightHomologyMapData.natTransApp h
    (sectionsLocalizationComparison R r (PrimeSpectrum.basicOpen q))
  change IsIso (ShortComplex.homologyMap ((I.sc n).mapNatTrans
    (sectionsLocalizationComparison R r (PrimeSpectrum.basicOpen q))))
  rw [γ.homologyMap_eq]
  change IsIso ((h.map F).homologyIso.hom ≫
    sectionsLocalizationLift R r (PrimeSpectrum.basicOpen q) h.H ≫ (h.map G).homologyIso.inv)
  infer_instance

end Quillen.PerfectComplexes.Affine
