/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnit
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnitSelfTrackKZero
public import Quillen.Waldhausen.GrothendieckComparison.SmallModelHomExt

/-!
# Original K-zero unit operations through the actual bounded-flat inclusion

The original object-generator theorem identifies the two homomorphisms using their literal
scalar automorphisms and the actual inclusion. No replacement boundary or all-stage comparison
is used. Flatness is needed only for the geometric perfect pullback occurring in the statement.
-/
@[expose] public section
open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The actual inclusion carries the literal bounded-flat scalar component to the perfect one. -/
theorem boundedFlatPerfectUnitComponent_inclusion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] (q : (Γ(X, ⊤))ˣ) :
    Functor.whiskerRight (boundedFlatPerfectPullbackUnitIso f q).hom
      (boundedFlatPerfectInclusion X) =
    Functor.whiskerLeft (boundedFlatPerfectInclusion Y) (perfectFlatPullbackUnitIso f q).hom := by
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

/-- Actual model inclusion intertwines the original K-zero unit operations on all classes. -/
theorem boundedFlatPerfectToPerfectKMap_comp_unitKZero {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] (q : (Γ(X, ⊤))ˣ) :
    (boundedFlatPerfectToPerfectKMap X 1).comp
      (originalKSelfTrackOperation (boundedFlatPerfectWaldhausen Y)
        (boundedFlatPerfectWaldhausen X) (boundedFlatPerfectUnitHomotopy f q) 0) =
      (originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
        (perfectFlatUnitHomotopy f q) 0).comp (boundedFlatPerfectToPerfectKMap Y 0) := by
  apply AlgebraicGrothendieck.kZero_hom_ext_ofSmallModel (boundedFlatPerfectWaldhausen Y)
  intro K
  change KMap (boundedFlatPerfectInclusion_exact X) 1
    (originalKSelfTrackOperation _ _ (boundedFlatPerfectUnitHomotopy f q) 0
      ((boundedFlatPerfectWaldhausen Y).kZeroObjectClass K)) =
    originalKSelfTrackOperation _ _ (perfectFlatUnitHomotopy f q) 0
      (KMap (boundedFlatPerfectInclusion_exact Y) 0
        ((boundedFlatPerfectWaldhausen Y).kZeroObjectClass K))
  rw [KMap_kZeroObjectClass]
  change KMap (boundedFlatPerfectInclusion_exact X) 1
    (originalKSelfTrackOperation _ _
      (exactOriginalPrespectrumIsoHomotopy _ _ (boundedFlatPerfectPullback_exact f)
        (boundedFlatPerfectPullback_exact f) (boundedFlatPerfectPullbackUnitIso f q)) 0 _) =
    originalKSelfTrackOperation _ _
      (exactOriginalPrespectrumIsoHomotopy _ _ (perfectFlatPullback_waldhausenExact f)
        (perfectFlatPullback_waldhausenExact f) (perfectFlatPullbackUnitIso f q)) 0 _
  rw [originalKSelfTrackOperation_object, originalKSelfTrackOperation_object,
    KMap_automorphismKOneClass]
  apply congrArg (perfectWaldhausen X).automorphismKOneClass
  apply Iso.ext
  exact congrArg (fun η => η.app K) (boundedFlatPerfectUnitComponent_inclusion f q)

end Quillen.PerfectComplexes
