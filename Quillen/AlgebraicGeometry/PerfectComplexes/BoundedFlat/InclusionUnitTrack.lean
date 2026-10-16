/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.ConeHomotopyComparison
public import Quillen.Waldhausen.SConstruction.Iterated.NormalizationTrackPasting
public import Quillen.Topology.Prespectrum.RelativeHomotopyIntertwining

/-!
# Original global-unit compatibility with bounded-flat inclusion

The faithful inclusions preserve the actual ambient scalar transformation. The two binary
normalization pasting comparisons therefore intertwine the unchanged bounded-flat and perfect
unit homotopies along the original reversed-first, forward-second inclusion track.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- Inclusion preserves the actual global-unit transformation on geometric flat pullback. -/
theorem boundedFlatPerfectPullbackUnitIso_inclusion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] (r : (Γ(X, ⊤))ˣ) :
    Functor.whiskerRight (boundedFlatPerfectPullbackUnitIso f r).hom
      (boundedFlatPerfectInclusion X) =
    Functor.whiskerLeft (boundedFlatPerfectInclusion Y) (perfectFlatPullbackUnitIso f r).hom := by
  apply NatTrans.ext
  funext K
  apply (locallyPerfect X).ι.map_injective
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app,
    boundedFlatPerfectPullbackUnitIso, perfectFlatPullbackUnitIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.isoWhiskerLeft_hom, Category.id_comp]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  simp only [Category.comp_id]
  simp only [boundedFlatPerfectGlobalUnitIso, perfectGlobalUnitIso,
    Functor.fullyFaithfulCancelRight_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app]
  change (boundedFlatPerfect X).ι.map ((boundedFlatPerfect X).ι.preimage _) = _
  rw [Functor.map_preimage, Functor.map_preimage]
  rfl

/-- The original bounded-flat and perfect unit tracks intertwine along the original full
flat-pullback inclusion track, including both of its binary normalization tracks. -/
def boundedFlatPerfectInclusionUnitTrack {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] (r : (Γ(X, ⊤))ˣ) :
    (((boundedFlatPerfectUnitHomotopy f r).postcomp
      (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
        (boundedFlatPerfectInclusion_exact X))).trans
      (boundedFlatPerfectInclusionFlatPullbackHomotopy f)).RelHomotopy
    ((boundedFlatPerfectInclusionFlatPullbackHomotopy f).trans
      (Homotopy.precomp
        (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Y) (perfectWaldhausen Y)
          (boundedFlatPerfectInclusion_exact Y)) (perfectFlatUnitHomotopy f r))) := by
  let hf := boundedFlatPerfectPullback_exact f
  let hi := boundedFlatPerfectInclusion_exact X
  let hj := boundedFlatPerfectInclusion_exact Y
  let hp := perfectFlatPullback_waldhausenExact f
  let U := exactOriginalPrespectrumHomotopy _ _ (hf.comp hi) (hf.comp hi)
    (Functor.whiskerRight (boundedFlatPerfectPullbackUnitIso f r).hom
      (boundedFlatPerfectInclusion X))
    (fun K ↦ hi.weak _ ((boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance))
  let C := exactOriginalPrespectrumMapCompHomotopy _ _ _ hf hi
  let D := exactOriginalPrespectrumMapCompHomotopy _ _ _ hj hp
  let V := (boundedFlatPerfectUnitHomotopy f r).postcomp
    (exactOriginalPrespectrumMap _ _ hi)
  let W := Homotopy.precomp (exactOriginalPrespectrumMap _ _ hj) (perfectFlatUnitHomotopy f r)
  have JC : (U.trans C).RelHomotopy (C.trans V) :=
    exactNormalizationLeftTrackPasting hf hf hi (boundedFlatPerfectPullbackUnitIso f r).hom
      (fun _ ↦ (boundedFlatPerfectWaldhausen X).weq_iso _ inferInstance)
  have JD : (U.trans D).RelHomotopy (D.trans W) := by
    dsimp only [U]
    simp only [boundedFlatPerfectPullbackUnitIso_inclusion f r]
    exact exactNormalizationRightTrackPasting hj hp hp (perfectFlatPullbackUnitIso f r).hom
      (fun _ ↦ (perfectWaldhausen X).weq_iso _ inferInstance)
  exact Homotopy.RelHomotopy.intertwine C D U V W JC.symm JD.symm

end Quillen.PerfectComplexes
