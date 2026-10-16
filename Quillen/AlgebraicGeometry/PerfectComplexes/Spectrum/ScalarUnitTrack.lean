/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlatPullbackRestriction


public import Quillen.AlgebraicGeometry.PerfectComplexes.ScalarLaurentClassComparison
public import Quillen.Waldhausen.SConstruction.Iterated.NormalizationTrackPasting
public import Quillen.Waldhausen.SConstruction.Iterated.ExactPastingHomotopy
public import Quillen.Topology.Prespectrum.RelativeHomotopyIntertwining

/-!
# Whole original scalar restriction and flat-unit tracks

The actual restricted scalar transformation intertwines the unchanged flat-unit transformation.
The comparison retains the reversed binary normalization track followed by the actual
restriction/flat-pullback isomorphism. Every level, basepoint and independent structure time is
retained. No scalar-cofiber boundary equation follows merely from this construction.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The actual normalized open-restriction prespectrum map. -/
def perfectOpenScalarRestrictionMap :
    originalPrespectrum (perfectOpenWeakWaldhausen j) ⟶
      originalPrespectrum (perfectWaldhausen U) :=
  exactOriginalPrespectrumMap _ _ (perfectOpenRestrict_waldhausenExact j)

/-- The comparison is exactly reversed normalization followed by the original geometric iso. -/
def perfectOpenRestrictionFlatHomotopy :
    Homotopy
      (exactOriginalPrespectrumMap _ _ (changeWeak_exact (perfectOpenNested j)) ≫
        perfectOpenScalarRestrictionMap j) (perfectFlatPrespectrumMap j) :=
  (exactOriginalPrespectrumMapCompHomotopy _ _ _
    (changeWeak_exact (perfectOpenNested j)) (perfectOpenRestrict_waldhausenExact j)).symm.trans
      (exactOriginalPrespectrumIsoHomotopy _ _
        ((changeWeak_exact (perfectOpenNested j)).comp (perfectOpenRestrict_waldhausenExact j))
        (perfectFlatPullback_waldhausenExact j) (perfectOpenRestrictionFlatIso j))

variable (r : Γ(X, ⊤)) (q : (Γ(U, ⊤))ˣ) (hq : j.appTop r = ↑q)

/-- The literal scalar gives its original canonically rebased whole self-track. -/
def perfectOpenScalarPrespectrumHomotopy :
    Homotopy (exactOriginalPrespectrumMap _ _ (changeWeak_exact (perfectOpenNested j)))
      (exactOriginalPrespectrumMap _ _ (changeWeak_exact (perfectOpenNested j))) :=
  exactOriginalPrespectrumHomotopy (perfectWaldhausen X) (perfectOpenWeakWaldhausen j)
    (changeWeak_exact (perfectOpenNested j)) (changeWeak_exact (perfectOpenNested j))
    (perfectGlobalScalar X r) (perfectGlobalScalar_openWeak j r q hq)

include hq in
/-- The entire actual transformation square follows from the original termwise scalar equation. -/
theorem perfectOpenScalarRestrictionTransformation :
    Functor.whiskerRight (perfectGlobalScalar X r) (perfectRestrict j) ≫
        (perfectOpenRestrictionFlatIso j).hom =
      (perfectOpenRestrictionFlatIso j).hom ≫ (perfectFlatPullbackUnitIso j q).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    perfectOpenRestrictionFlatIso, Iso.trans_hom, Functor.leftUnitor_hom_app,
    perfectFlatPullbackUnitIso, Iso.symm_hom, Functor.rightUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.id_comp]
  rw [perfectRestrict_scalar_eq_globalUnit j K r q hq]
  exact ((perfectGlobalUnitIso U q).hom.naturality
    ((perfectRestrictIsoFlatPullback j).hom.app K)).symm

/-- The specified full scalar track intertwines the actual flat-unit track along the unchanged
reversed-first normalization and forward geometric comparison. -/
def perfectOpenScalarRestrictionUnitTrack :
    (((perfectOpenScalarPrespectrumHomotopy j r q hq).postcomp
      (perfectOpenScalarRestrictionMap j)).trans
        (perfectOpenRestrictionFlatHomotopy j)).RelHomotopy
      ((perfectOpenRestrictionFlatHomotopy j).trans (perfectFlatUnitHomotopy j q)) := by
  let hF := changeWeak_exact (perfectOpenNested j)
  let hR := perfectOpenRestrict_waldhausenExact j
  let hP := perfectFlatPullback_waldhausenExact j
  let eta := perfectGlobalScalar X r
  let hEta := perfectGlobalScalar_openWeak j r q hq
  let e := perfectOpenRestrictionFlatIso j
  let Ueta := exactOriginalPrespectrumHomotopy _ _ (hF.comp hR) (hF.comp hR)
    (Functor.whiskerRight eta (perfectRestrict j)) (fun K => hR.weak _ (hEta K))
  let C := exactOriginalPrespectrumMapCompHomotopy _ _ _ hF hR
  let D := exactOriginalPrespectrumIsoHomotopy _ _ (hF.comp hR) hP e
  let Veta := (perfectOpenScalarPrespectrumHomotopy j r q hq).postcomp
    (perfectOpenScalarRestrictionMap j)
  let Hq := perfectFlatUnitHomotopy j q
  have JC : (Ueta.trans C).RelHomotopy (C.trans Veta) :=
    exactNormalizationLeftTrackPasting hF hF hR eta hEta
  have JD : (Ueta.trans D).RelHomotopy (D.trans Hq) :=
    exactOriginalPrespectrumPastingHomotopy _ _ (hF.comp hR) (hF.comp hR) hP hP
      (Functor.whiskerRight eta (perfectRestrict j)) e.hom e.hom
      (perfectFlatPullbackUnitIso j q).hom
      (fun K => hR.weak _ (hEta K)) (fun _ => (perfectWaldhausen U).weq_iso _ inferInstance)
      (fun _ => (perfectWaldhausen U).weq_iso _ inferInstance)
      (fun _ => (perfectWaldhausen U).weq_iso _ inferInstance)
      (perfectOpenScalarRestrictionTransformation j r q hq)
  exact Homotopy.RelHomotopy.intertwine C D Ueta Veta Hq JC.symm JD.symm

end Quillen.PerfectComplexes
