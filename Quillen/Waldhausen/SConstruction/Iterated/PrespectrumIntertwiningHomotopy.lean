/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumPastingHomotopy
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopyNaturality
public import Quillen.Topology.Prespectrum.HomotopyTransport
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels

/-!
# Whole original transformation tracks across a Model comparison

An actual intertwining equation gives the relative comparison of the original postwhiskered
and prewhiskered loops across the unchanged comparison track. All levels, including original
zero-level loops, and independent structure parameters are retained.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor Quillen.LoopPrespectrum
universe u
namespace Quillen.Waldhausen.IteratedS

/-- A genuine transformation square preserves the original two whole track pastings. -/
def prespectrumTransformationIntertwiningHomotopy {V W T U : Model.{u}}
    (F : V ⟶ W) (G : T ⟶ U) (a : V ⟶ T) (b : W ⟶ U)
    (η : F.functor ⟶ F.functor) (θ : G.functor ⟶ G.functor)
    (i : (F ≫ b).functor ⟶ (a ≫ G).functor)
    (hη : ∀ X, W.waldhausen.weq (η.app X))
    (hθ : ∀ X, U.waldhausen.weq (θ.app X))
    (hi : ∀ X, U.waldhausen.weq (i.app X))
    (he : whiskerRight η b.functor ≫ i = i ≫ whiskerLeft a.functor θ) :
    (((prespectrumTransformationHomotopy η hη).postcomp (prespectrumMap b)).trans
      ((prespectrumTransformationHomotopy i hi).cast
        (prespectrumFunctor.map_comp F b) (prespectrumFunctor.map_comp a G))).RelHomotopy
    (((prespectrumTransformationHomotopy i hi).cast
      (prespectrumFunctor.map_comp F b) (prespectrumFunctor.map_comp a G)).trans
        (Homotopy.precomp (prespectrumMap a) (prespectrumTransformationHomotopy θ hθ))) := by
  let J := prespectrumPastingHomotopy
    (F := F ≫ b) (G := F ≫ b) (G' := a ≫ G) (H := a ≫ G)
    (whiskerRight η b.functor) i i (whiskerLeft a.functor θ)
    (fun X ↦ b.exact.weak _ (hη X)) hi hi (fun X ↦ hθ (a.functor.obj X)) he
  refine J.ofLevels _ _ ?_ ?_
  · intro n
    apply Homotopy.trans_level_congr
    · exact (prespectrumTransformationHomotopy_postcomp_level η hη b n).symm
    · rfl
  · intro n
    apply Homotopy.trans_level_congr
    · rfl
    · exact (prespectrumTransformationHomotopy_precomp_level θ hθ a n).symm

end Quillen.Waldhausen.IteratedS
