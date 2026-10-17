/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Homology
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.Affine.CounitCriterion
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.Affine.OpenSectionsLocalization
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSectionsPushforward

/-!
# The actual qc-open derived pushforward counit on an affine scheme

For a lower-bounded termwise-injective complex on a quasi-compact open of
Spec R, with quasicoherent homology, the ORIGINAL counit from the associated
sheaf complex of global sections to its actual termwise direct image is a
quasi-isomorphism. Quasicoherence of the direct-image homology is a conclusion.
No upper bound, termwise quasicoherence, noetherianity or ambient-perfectness
hypothesis is imposed.

The proof uses genuine finite-cover localization of sections on the open,
the original strict shrinking square, and actual isomorphisms between the
pushforward sections on an open and its intersection with the image. Basis
exactness then detects the literal counit. It does not assume exactness of
ordinary direct image or quasicoherence of its terms.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

open AlgebraicGeometry.Scheme


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes.Affine

lemma isIso_affineSectionsComplexRestriction_pushforward {R : CommRingCat.{u}}
    {Y : Scheme.{u}} (j : Y ⟶ Spec R) (I : CochainComplex Y.Modules ℤ)
    {U V : (Spec R).Opens} (h : U ≤ V) (heq : j ⁻¹ᵁ U = j ⁻¹ᵁ V) :
    IsIso (affineSectionsComplexRestriction R h ((pushforwardComplex j).obj I)) := by
  have hcomp (n : ℤ) : IsIso
      ((affineSectionsComplexRestriction R h ((pushforwardComplex j).obj I)).f n) :=
    Modules.QuasiCoherent.AffineSections.isIso_pushforward_modulesSpecToSheaf_map_of_preimage_eq
      j (I.X n) (homOfLE h) heq
  exact HomologicalComplex.Hom.isIso_of_components _

lemma quasiIso_principalComparison_pushforward_of_openComparison {R : CommRingCat.{u}}
    (W : (Spec R).Opens) (I : CochainComplex W.toScheme.Modules ℤ) (r : R)
    (h : QuasiIso (sectionsLocalizationComplexComparison R r W
      ((pushforwardComplex W.ι).obj I))) :
    QuasiIso (principalSectionsScalarComplexComparison R r ((pushforwardComplex W.ι).obj I)) := by
  let J := (pushforwardComplex W.ι).obj I
  have ht : W.ι ⁻¹ᵁ W = ⊤ := by
    simpa only [Scheme.Opens.opensRange_ι] using Scheme.Hom.preimage_opensRange W.ι
  have ha := isIso_affineSectionsComplexRestriction_pushforward W.ι I
    (le_top : W ≤ ⊤) (by simp [ht])
  have hb := isIso_affineSectionsComplexRestriction_pushforward W.ι I
    (inf_le_inf (le_top : W ≤ ⊤) (le_refl (PrimeSpectrum.basicOpen r))) (by
      rw [Scheme.Hom.preimage_inf, Scheme.Hom.preimage_inf, ht]
      simp)
  have htop : QuasiIso (sectionsLocalizationComplexComparison R r ⊤ J) := by
    rw [← quasiIso_iff_comp_right _
      (affineSectionsComplexRestriction R (inf_le_inf (le_top : W ≤ ⊤) le_rfl) J),
      ← sectionsLocalizationComplexComparison_restrict R r (le_top : W ≤ ⊤) J]
    let := h
    infer_instance
  let e := (NatIso.mapHomologicalComplex
    (affineSectionsAtCongr R (top_inf_eq (PrimeSpectrum.basicOpen r))) (.up ℤ)).app J
  have he : sectionsLocalizationComplexComparison R r ⊤ J ≫ e.hom =
      principalSectionsScalarComplexComparison R r J := by
    ext n : 1
    exact congrArg (fun t => t.app (J.X n)) (sectionsLocalizationComparison_top R r)
  rw [← he]
  infer_instance

lemma quasiIso_pushforward_counit_of_openComparisons {R : CommRingCat.{u}}
    (W : (Spec R).Opens) (I : CochainComplex W.toScheme.Modules ℤ)
    (h : ∀ r : R, QuasiIso (sectionsLocalizationComplexComparison R r W
      ((pushforwardComplex W.ι).obj I))) :
    QuasiIso (associatedSectionsCounit R ((pushforwardComplex W.ι).obj I)) :=
  quasiIso_associatedSectionsCounit_of_principalComparisons R _
    (fun r => quasiIso_principalComparison_pushforward_of_openComparison W I r (h r))


lemma quasiIso_openPushforward_associatedSectionsCounit {R : CommRingCat.{u}}
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (I : CochainComplex W.toScheme.Modules ℤ) (a : ℤ) (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n)) (hqc : ∀ n, (I.homology n).IsQuasicoherent) :
    QuasiIso (associatedSectionsCounit R ((pushforwardComplex W.ι).obj I)) := by
  let J := (pushforwardComplex W.ι).obj I
  have hJb (n : ℤ) (hn : n < a) : IsZero (J.X n) :=
    (Scheme.Modules.pushforward W.ι).map_isZero (hbound n hn)
  have hJi (n : ℤ) : Injective (J.X n) := by
    let := hinj n
    exact injective_pushforward W.ι (I.X n)
  have hJqc (n : ℤ) : (((restrict W.ι).obj J).homology n).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent W.toScheme.ringCatSheaf).prop_of_iso
      (((HomologicalComplex.homologyFunctor W.toScheme.Modules (.up ℤ) n).mapIso
        ((pushforwardComplexRestrictIso W.ι).app I)).symm) (hqc n)
  exact quasiIso_pushforward_counit_of_openComparisons W I (fun r =>
    quasiIso_sectionsLocalizationComplexComparison_of_quasicoherent_on_open r J a
      hJb hJi W hW hJqc)

lemma openPushforward_quasicoherent_homology {R : CommRingCat.{u}}
    (W : (Spec R).Opens) (hW : IsCompact (W : Set (Spec R)))
    (I : CochainComplex W.toScheme.Modules ℤ) (a : ℤ) (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n)) (hqc : ∀ n, (I.homology n).IsQuasicoherent) (n : ℤ) :
    (((pushforwardComplex W.ι).obj I).homology n).IsQuasicoherent := by
  let J := (pushforwardComplex W.ι).obj I
  let := quasiIso_openPushforward_associatedSectionsCounit W hW I a hbound hinj hqc
  have : IsIso (HomologicalComplex.homologyMap (associatedSectionsCounit R J) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ _).mp inferInstance
  have h := AlgebraicGeometry.Scheme.Modules.QuasiCoherent.quasicoherent_homology
    ((associatedComplex R).obj ((sectionsComplex R).obj J)) (fun i => by
      change ((tilde.functor R).obj _).IsQuasicoherent
      infer_instance) n
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (asIso (HomologicalComplex.homologyMap (associatedSectionsCounit R J) n)) h
end Quillen.PerfectComplexes.Affine
