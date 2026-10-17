/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnitKZeroComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalUnitKOperation
public import Quillen.Waldhausen.SConstruction.Iterated.NormalizationTrackPasting
public import Quillen.Topology.Prespectrum.RelativeHomotopyIntertwining

/-!
# Original unit operations through bounded-flat inclusion in every degree

The two original exact-functor normalization homotopies compare actual inclusion and flat
pullback. Their full scalar naturality pasting intertwines the original unit loops. The
resulting original K-operation equality holds in every connective degree; it uses no cone
comparison or positivity-detection theorem.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- The original reversed-first, forward-second normalization comparison for actual inclusion.
-/
def boundedFlatPerfectUnitInclusionHomotopy {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    Homotopy
      (boundedFlatPerfectPrespectrumMap f ≫
        exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
          (boundedFlatPerfectInclusion_exact X))
      (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Y) (perfectWaldhausen Y)
        (boundedFlatPerfectInclusion_exact Y) ≫ perfectFlatPrespectrumMap f) :=
  (exactOriginalPrespectrumMapCompHomotopy _ _ _
    (boundedFlatPerfectPullback_exact f) (boundedFlatPerfectInclusion_exact X)).symm.trans
      (exactOriginalPrespectrumMapCompHomotopy _ _ _
        (boundedFlatPerfectInclusion_exact Y) (perfectFlatPullback_waldhausenExact f))

/-- The original bounded-flat and perfect unit tracks intertwine along the original full
flat-pullback inclusion track, including both of its binary normalization tracks. -/
def boundedFlatPerfectUnitInclusionTrack {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] (r : (Γ(X, ⊤))ˣ) :
    (((boundedFlatPerfectUnitHomotopy f r).postcomp
      (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
        (boundedFlatPerfectInclusion_exact X))).trans
      (boundedFlatPerfectUnitInclusionHomotopy f)).RelHomotopy
    ((boundedFlatPerfectUnitInclusionHomotopy f).trans
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
    simp only [boundedFlatPerfectUnitComponent_inclusion f r]
    exact exactNormalizationRightTrackPasting hj hp hp (perfectFlatPullbackUnitIso f r).hom
      (fun _ ↦ (perfectWaldhausen X).weq_iso _ inferInstance)
  exact Homotopy.RelHomotopy.intertwine C D U V W JC.symm JD.symm


/-- The actual bounded-flat inclusion preserves the original unit operation in every degree. -/
theorem boundedFlatPerfectToPerfectKMap_comp_unitOperation {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] (q : (Γ(X, ⊤))ˣ) (n : ℕ) :
    (boundedFlatPerfectToPerfectKMap X (n + 1)).comp
      (originalKSelfTrackOperation (boundedFlatPerfectWaldhausen Y)
        (boundedFlatPerfectWaldhausen X) (boundedFlatPerfectUnitHomotopy f q) n) =
      (originalKSelfTrackOperation (perfectWaldhausen Y) (perfectWaldhausen X)
        (perfectFlatUnitHomotopy f q) n).comp (boundedFlatPerfectToPerfectKMap Y n) := by
  unfold boundedFlatPerfectToPerfectKMap
  rw [← originalKSelfTrackOperation_postcomp, ← originalKSelfTrackOperation_precomp]
  exact originalKSelfTrackOperation_intertwine
    (boundedFlatPerfectWaldhausen Y) (perfectWaldhausen X)
    ((boundedFlatPerfectUnitHomotopy f q).postcomp
      (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen X) (perfectWaldhausen X)
        (boundedFlatPerfectInclusion_exact X)))
    (Homotopy.precomp
      (exactOriginalPrespectrumMap (boundedFlatPerfectWaldhausen Y) (perfectWaldhausen Y)
        (boundedFlatPerfectInclusion_exact Y)) (perfectFlatUnitHomotopy f q))
    (boundedFlatPerfectUnitInclusionHomotopy f)
    (boundedFlatPerfectUnitInclusionTrack f q) n

end Quillen.PerfectComplexes
