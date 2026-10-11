/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopyNaturality

/-! Original degree-zero loop evaluation and independent structure time under actual whiskering. -/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace Quillen.Tests.PrespectrumHomotopyNaturality
variable {V W T : Model.{u}} {F G : V ⟶ W}
  (η : F.functor ⟶ G.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))

lemma postcomp_original_zero_loop (J : W ⟶ T) (s q : unitInterval)
    (γ : Path (stagePoint 0 V) (stagePoint 0 V)) :
    (show Path (stagePoint 0 T) (stagePoint 0 T) from
      (prespectrumTransformationHomotopy (F := F ≫ J) (G := G ≫ J)
        (whiskerRight η J.functor) (fun A ↦ J.exact.weak _ (hη A))).level 0 (s, γ)) q =
      SSet.toTop.map ((stages 0).map J) (stageTransformationTopHomotopy 0 η hη (s, γ q)) := by
  rw [prespectrumTransformationHomotopy_postcomp_level]
  rfl

lemma precomp_original_zero_loop (J : T ⟶ V) (s q : unitInterval)
    (γ : Path (stagePoint 0 T) (stagePoint 0 T)) :
    (show Path (stagePoint 0 W) (stagePoint 0 W) from
      (prespectrumTransformationHomotopy (F := J ≫ F) (G := J ≫ G)
        (whiskerLeft J.functor η) (fun A ↦ hη (J.functor.obj A))).level 0 (s, γ)) q =
      stageTransformationTopHomotopy 0 η hη
        (s, SSet.toTop.map ((stages 0).map J) (γ q)) := by
  rw [prespectrumTransformationHomotopy_precomp_level]
  rfl

lemma original_independent_structure (J : W ⟶ T) (n : ℕ) (s t : unitInterval)
    (x : (prespectrum V).space n) :
    (prespectrumTransformationHomotopy (F := F ≫ J) (G := G ≫ J)
      (whiskerRight η J.functor) (fun A ↦ J.exact.weak _ (hη A))).level (n + 1)
        (s, (prespectrum V).structureMap n x t) =
      (prespectrum T).structureMap n
        ((prespectrumTransformationHomotopy (F := F ≫ J) (G := G ≫ J)
          (whiskerRight η J.functor) (fun A ↦ J.exact.weak _ (hη A))).level n (s, x)) t :=
  (prespectrumTransformationHomotopy (F := F ≫ J) (G := G ≫ J)
    (whiskerRight η J.functor) (fun A ↦ J.exact.weak _ (hη A))).comm n s x t

end Quillen.Tests.PrespectrumHomotopyNaturality
