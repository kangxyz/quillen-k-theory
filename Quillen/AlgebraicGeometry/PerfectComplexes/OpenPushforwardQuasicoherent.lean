/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.OpenPushforwardCounit
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenPushforwardBaseChange
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.InjectiveRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Quasicoherent homology of actual quasi-compact open direct images

The original termwise direct image of a lower-bounded injective complex with
quasicoherent homology has quasicoherent homology along every quasi-compact
open immersion. The ambient scheme need not be quasi-compact or separated.
The proof uses actual affine base change, preservation of injectives under
restriction, and the established affine direct-image counit theorem.

No upper bound or quasicoherence of injective terms is assumed. Ordinary
direct image is not asserted exact; perfection of its result is not claimed.
-/
@[expose] public section

open ModuleCat
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
namespace Quillen.PerfectComplexes

/-- The original affine theorem transported through the genuine open-image isomorphism. -/
lemma spec_openPushforward_quasicoherent_homology {R : CommRingCat.{u}}
    {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j] [CompactSpace U]
    (I : Complex U) (a : ℤ) (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n)) (hqc : ∀ n, (I.homology n).IsQuasicoherent) (n : ℤ) :
    (((pushforwardComplex j).obj I).homology n).IsQuasicoherent := by
  let e := j.isoOpensRange
  let I' := (restrict e.inv).obj I
  have hb (m : ℤ) (hm : m < a) : IsZero (I'.X m) :=
    (Scheme.Modules.restrictFunctor e.inv).map_isZero (hbound m hm)
  have hi (m : ℤ) : Injective (I'.X m) := by
    let := hinj m
    exact AlgebraicGeometry.Scheme.Modules.injective_restrict e.inv (I.X m)
  have hq (m : ℤ) : (I'.homology m).IsQuasicoherent :=
    Affine.quasicoherent_homology_restrict e.inv I hqc m
  have hp := Affine.openPushforward_quasicoherent_homology j.opensRange
    (isCompact_range j.continuous) I' a hb hi hq n
  let c : pushforwardComplex j ≅ restrict e.inv ⋙ pushforwardComplex j.opensRange.ι :=
    eqToIso (congrArg pushforwardComplex j.isoOpensRange_hom_ι.symm) ≪≫
    (pushforwardComplexCompIso e.hom j.opensRange.ι).symm ≪≫
    Functor.isoWhiskerRight (pushforwardComplexOfIso e) _
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (((HomologicalComplex.homologyFunctor _ (.up ℤ) n).mapIso (c.app I)).symm) hp

/-- Quasi-compact open direct image of a lower-bounded injective QC-homology complex
has QC homology on any ambient scheme. -/
lemma openPushforward_quasicoherent_homology {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (I : Complex U) (a : ℤ) (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n)) (hqc : ∀ n, (I.homology n).IsQuasicoherent) (n : ℤ) :
    (((pushforwardComplex j).obj I).homology n).IsQuasicoherent := by
  let J := (pushforwardComplex j).obj I
  apply AlgebraicGeometry.Scheme.Modules.QuasiCoherent.quasicoherent_of_affineCharts
  intro R k _
  let p := pullback.fst j k
  let q := pullback.snd j k
  let : CompactSpace (pullback j k : Scheme.{u}) := QuasiCompact.compactSpace_of_compactSpace q
  let I' := (restrict p).obj I
  have hb (m : ℤ) (hm : m < a) : IsZero (I'.X m) :=
    (Scheme.Modules.restrictFunctor p).map_isZero (hbound m hm)
  have hi (m : ℤ) : Injective (I'.X m) := by
    let := hinj m
    exact AlgebraicGeometry.Scheme.Modules.injective_restrict p (I.X m)
  have hq (m : ℤ) : (I'.homology m).IsQuasicoherent :=
    Affine.quasicoherent_homology_restrict p I hqc m
  have hs := spec_openPushforward_quasicoherent_homology q I' a hb hi hq n
  let c := openPushforwardComplexBaseChangeIso p q j k pullback.condition (by
    intro v hv
    rw [IsOpenImmersion.range_pullbackSnd]
    exact hv)
  have hr : (((restrict k).obj J).homology n).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (((HomologicalComplex.homologyFunctor _ (.up ℤ) n).mapIso (c.app I)).symm) hs
  have hm : ((J.homology n).restrict k).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (restrictHomologyIso k J n) hr
  exact hm

/-- A compact open source and quasi-separated target supply quasi-compactness of the map. -/
lemma compact_openPushforward_quasicoherent_homology {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiSeparatedSpace X] [CompactSpace U]
    (I : Complex U) (a : ℤ) (hbound : ∀ n, n < a → IsZero (I.X n))
    (hinj : ∀ n, Injective (I.X n)) (hqc : ∀ n, (I.homology n).IsQuasicoherent) (n : ℤ) :
    (((pushforwardComplex j).obj I).homology n).IsQuasicoherent :=
  openPushforward_quasicoherent_homology j I a hbound hinj hqc n

end Quillen.PerfectComplexes
