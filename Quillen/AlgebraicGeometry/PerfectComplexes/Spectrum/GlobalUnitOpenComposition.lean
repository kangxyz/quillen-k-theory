/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalUnitKOneRestriction
public import Quillen.Waldhausen.SConstruction.Iterated.NormalizationTrackPasting
public import Quillen.Waldhausen.SConstruction.Iterated.ExactPastingHomotopy
public import Quillen.Topology.Prespectrum.RelativeHomotopyIntertwining
public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationIntertwining
public import Quillen.Waldhausen.SConstruction.Iterated.SelfTrackKOperationNaturality

/-!
# Whole flat-unit tracks under open restriction and geometric composition

The original open restriction of a flat-pullback unit track intertwines the unit track on
its actual geometric composite. The comparison retains the reversed binary normalization
track followed by the original restriction/flat-pullback and flat-composition isomorphisms.
Its full two-time family gives the original K-operation equation in every connective degree.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {U X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (i : U ⟶ X) [IsOpenImmersion i]

/-- The original open/flat comparison followed by the inverse geometric composition iso. -/
def perfectFlatOpenCompositionIso :
    perfectFlatPullback f ⋙ perfectRestrict i ≅ perfectFlatPullback (i ≫ f) :=
  Functor.isoWhiskerLeft (perfectFlatPullback f) (perfectRestrictIsoFlatPullback i) ≪≫
    (perfectFlatPullbackCompIso i f).symm

/-- The original reversed normalization and forward geometric comparison, with exact endpoints. -/
def perfectFlatOpenCompositionHomotopy :
    Homotopy
      (perfectFlatPrespectrumMap f ≫
        exactOriginalPrespectrumMap _ _ (perfectRestrict_waldhausenExact i))
      (perfectFlatPrespectrumMap (i ≫ f)) :=
  (exactOriginalPrespectrumMapCompHomotopy _ _ _
    (perfectFlatPullback_waldhausenExact f) (perfectRestrict_waldhausenExact i)).symm.trans
      (exactOriginalPrespectrumIsoHomotopy _ _
        ((perfectFlatPullback_waldhausenExact f).comp (perfectRestrict_waldhausenExact i))
        (perfectFlatPullback_waldhausenExact (i ≫ f)) (perfectFlatOpenCompositionIso f i))

variable (q : (Γ(X, ⊤))ˣ)

/-- The actual restricted unit commutes with the original geometric composition isomorphism. -/
theorem perfectFlatUnitOpenCompositionTransformation :
    Functor.whiskerRight (perfectFlatPullbackUnitIso f q).hom (perfectRestrict i) ≫
        (perfectFlatOpenCompositionIso f i).hom =
      (perfectFlatOpenCompositionIso f i).hom ≫
        (perfectFlatPullbackUnitIso (i ≫ f)
          (Units.map i.appTop.hom.toMonoidHom q)).hom := by
  apply NatTrans.ext
  funext K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, perfectFlatPullbackUnitIso,
    Iso.trans_hom, Iso.symm_hom, Functor.rightUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Category.id_comp]
  have hc := congrArg Iso.hom
    (perfectRestrict_globalUnitIso_app i q ((perfectFlatPullback f).obj K))
  change (perfectRestrict i).map ((perfectGlobalUnitIso X q).hom.app
    ((perfectFlatPullback f).obj K)) = _ at hc
  have hf : (perfectGlobalUnitIso X q).hom.app ((perfectFlatPullback f).obj K) ≫
      𝟙 ((perfectFlatPullback f).obj K) =
        (perfectGlobalUnitIso X q).hom.app ((perfectFlatPullback f).obj K) :=
    Category.comp_id _
  have hp : (perfectGlobalUnitIso U (Units.map i.appTop.hom.toMonoidHom q)).hom.app
      ((perfectFlatPullback (i ≫ f)).obj K) ≫ 𝟙 ((perfectFlatPullback (i ≫ f)).obj K) =
        (perfectGlobalUnitIso U (Units.map i.appTop.hom.toMonoidHom q)).hom.app
          ((perfectFlatPullback (i ≫ f)).obj K) := Category.comp_id _
  rw [hf, hp, hc]
  exact ((perfectGlobalUnitIso U (Units.map i.appTop.hom.toMonoidHom q)).hom.naturality
    ((perfectFlatOpenCompositionIso f i).hom.app K)).symm

/-- The whole actual unit track intertwines along the original binary normalization comparison. -/
def perfectFlatUnitOpenCompositionTrack :
    (((perfectFlatUnitHomotopy f q).postcomp
      (exactOriginalPrespectrumMap _ _ (perfectRestrict_waldhausenExact i))).trans
        (perfectFlatOpenCompositionHomotopy f i)).RelHomotopy
      ((perfectFlatOpenCompositionHomotopy f i).trans
        (perfectFlatUnitHomotopy (i ≫ f) (Units.map i.appTop.hom.toMonoidHom q))) := by
  let hF := perfectFlatPullback_waldhausenExact f
  let hR := perfectRestrict_waldhausenExact i
  let hP := perfectFlatPullback_waldhausenExact (i ≫ f)
  let eta := (perfectFlatPullbackUnitIso f q).hom
  let hEta := fun K => (perfectWaldhausen X).weq_iso (eta.app K) inferInstance
  let e := perfectFlatOpenCompositionIso f i
  let Ueta := exactOriginalPrespectrumHomotopy _ _ (hF.comp hR) (hF.comp hR)
    (Functor.whiskerRight eta (perfectRestrict i)) (fun K => hR.weak _ (hEta K))
  let C := exactOriginalPrespectrumMapCompHomotopy _ _ _ hF hR
  let D := exactOriginalPrespectrumIsoHomotopy _ _ (hF.comp hR) hP e
  let Veta := (perfectFlatUnitHomotopy f q).postcomp (exactOriginalPrespectrumMap _ _ hR)
  let Hq := perfectFlatUnitHomotopy (i ≫ f) (Units.map i.appTop.hom.toMonoidHom q)
  have JC : (Ueta.trans C).RelHomotopy (C.trans Veta) :=
    exactNormalizationLeftTrackPasting hF hF hR eta hEta
  have JD : (Ueta.trans D).RelHomotopy (D.trans Hq) :=
    exactOriginalPrespectrumPastingHomotopy _ _ (hF.comp hR) (hF.comp hR) hP hP
      (Functor.whiskerRight eta (perfectRestrict i)) e.hom e.hom
      (perfectFlatPullbackUnitIso (i ≫ f) (Units.map i.appTop.hom.toMonoidHom q)).hom
      (fun K => hR.weak _ (hEta K)) (fun _ => (perfectWaldhausen U).weq_iso _ inferInstance)
      (fun _ => (perfectWaldhausen U).weq_iso _ inferInstance)
      (fun _ => (perfectWaldhausen U).weq_iso _ inferInstance)
      (perfectFlatUnitOpenCompositionTransformation f i q)
  exact Homotopy.RelHomotopy.intertwine C D Ueta Veta Hq JC.symm JD.symm

/-- The actual restriction preserves this unit operation on every original connective K-group. -/
theorem perfectFlatUnitHomotopy_originalKOperation_restrict_comp (n : ℕ) :
    (perfectKRestrict i (n + 1)).comp
        (originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
          (perfectFlatUnitHomotopy f q) n) =
      originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy (i ≫ f) (Units.map i.appTop.hom.toMonoidHom q)) n := by
  unfold perfectKRestrict
  rw [← originalKSelfTrackOperation_postcomp]
  exact originalKSelfTrackOperation_intertwine (perfectWaldhausen Y) (perfectWaldhausen U)
    ((perfectFlatUnitHomotopy f q).postcomp
      (exactOriginalPrespectrumMap _ _ (perfectRestrict_waldhausenExact i)))
    (perfectFlatUnitHomotopy (i ≫ f) (Units.map i.appTop.hom.toMonoidHom q))
    (perfectFlatOpenCompositionHomotopy f i) (perfectFlatUnitOpenCompositionTrack f i q) n

/-- Every original input retains the same actual pulled-back unit, including input degree zero. -/
theorem perfectFlatUnitHomotopy_originalKOperation_restrict_comp_apply
    (n : ℕ) (a : PerfectK Y n) :
    perfectKRestrict i (n + 1)
        (originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
          (perfectFlatUnitHomotopy f q) n a) =
      originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen U)
        (perfectFlatUnitHomotopy (i ≫ f) (Units.map i.appTop.hom.toMonoidHom q)) n a :=
  DFunLike.congr_fun (perfectFlatUnitHomotopy_originalKOperation_restrict_comp f i q n) a

end Quillen.PerfectComplexes
