/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumHomotopy
public import Quillen.Topology.Realization.HomotopyBridge

/-!
# Original transformation homotopies under strict exact-functor composition

The existing simplicial whiskering identities identify the full original realized tracks after
precomposition or postcomposition. Degree zero is checked on the actual based loops. Every time
slice is the original composed prespectrum map; no replacement homotopy is selected.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor MonoidalCategory Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Waldhausen.IteratedS

variable {V W T : Model.{u}} {F G : V ⟶ W}
  (η : F.functor ⟶ G.functor) (hη : ∀ A, W.waldhausen.weq (η.app A))

/-- The actual postwhiskered simplicial cylinder retains its original stage map. -/
lemma stageTransformationCylinder_postcomp (r : ℕ) (J : W ⟶ T) :
    stageTransformationCylinder r (F := F ≫ J) (G := G ≫ J)
      (whiskerRight η J.functor) (fun A ↦ J.exact.weak _ (hη A)) =
      stageTransformationCylinder r η hη ≫ (stages r).map J := by
  ext n z : 4
  exact stageTransformationFunction_postcomp r η hη J n z.1 z.2

/-- The actual prewhiskered simplicial cylinder retains its original stage map. -/
lemma stageTransformationCylinder_precomp (r : ℕ) (J : T ⟶ V) :
    stageTransformationCylinder r (F := J ≫ F) (G := J ≫ G)
      (whiskerLeft J.functor η) (fun A ↦ hη (J.functor.obj A)) =
      (stages r).map J ▷ Δ[1] ≫ stageTransformationCylinder r η hη := by
  ext n z : 4
  exact stageTransformationFunction_precomp r η hη J n z.1 z.2

/-- Postcomposition preserves every parameter of the original realized stage homotopy. -/
lemma stageTransformationTopHomotopy_postcomp (r : ℕ) (J : W ⟶ T)
    (s : unitInterval) (x : stageSpace r V) :
    stageTransformationTopHomotopy r (F := F ≫ J) (G := G ≫ J)
      (whiskerRight η J.functor) (fun A ↦ J.exact.weak _ (hη A)) (s, x) =
      SSet.toTop.map ((stages r).map J) (stageTransformationTopHomotopy r η hη (s, x)) := by
  change SSet.toTop.map (stageTransformationCylinder r (F := F ≫ J) (G := G ≫ J)
      (whiskerRight η J.functor) (fun A ↦ J.exact.weak _ (hη A)))
      ((realizationCylinderIso ((stages r).obj V)).inv (x, ULift.up s)) =
    SSet.toTop.map ((stages r).map J) (SSet.toTop.map (stageTransformationCylinder r η hη)
      ((realizationCylinderIso ((stages r).obj V)).inv (x, ULift.up s)))
  rw [stageTransformationCylinder_postcomp, Functor.map_comp]
  rfl

/-- Precomposition preserves every parameter of the original realized stage homotopy. -/
lemma stageTransformationTopHomotopy_precomp (r : ℕ) (J : T ⟶ V)
    (s : unitInterval) (x : stageSpace r T) :
    stageTransformationTopHomotopy r (F := J ≫ F) (G := J ≫ G)
      (whiskerLeft J.functor η) (fun A ↦ hη (J.functor.obj A)) (s, x) =
      stageTransformationTopHomotopy r η hη (s, SSet.toTop.map ((stages r).map J) x) := by
  let p := (realizationCylinderIso ((stages r).obj T)).inv (x, ULift.up s)
  have hn := ConcreteCategory.congr_hom
    (realizationCylinderIso_inv_naturality ((stages r).map J)) (x, ULift.up s)
  change SSet.toTop.map ((stages r).map J ▷ Δ[1]) p =
    (realizationCylinderIso ((stages r).obj V)).inv
      (SSet.toTop.map ((stages r).map J) x, ULift.up s) at hn
  change SSet.toTop.map (stageTransformationCylinder r (F := J ≫ F) (G := J ≫ G)
      (whiskerLeft J.functor η) (fun A ↦ hη (J.functor.obj A))) p =
    SSet.toTop.map (stageTransformationCylinder r η hη)
      ((realizationCylinderIso ((stages r).obj V)).inv
        (SSet.toTop.map ((stages r).map J) x, ULift.up s))
  rw [stageTransformationCylinder_precomp, Functor.map_comp]
  exact congrArg (SSet.toTop.map (stageTransformationCylinder r η hη)) hn

/-- Every entire original prespectrum homotopy level commutes with postcomposition, including
its actual degree-zero based-loop level. -/
lemma prespectrumTransformationHomotopy_postcomp_level (J : W ⟶ T) (n : ℕ) :
    (prespectrumTransformationHomotopy (F := F ≫ J) (G := G ≫ J)
      (whiskerRight η J.functor) (fun A ↦ J.exact.weak _ (hη A))).level n =
    ((prespectrumTransformationHomotopy η hη).postcomp (prespectrumMap J)).level n := by
  cases n with
  | zero =>
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    apply Path.ext
    funext q
    change Path (stagePoint 0 V) (stagePoint 0 V) at x
    exact stageTransformationTopHomotopy_postcomp η hη 0 J s (x q)
  | succ r =>
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    exact stageTransformationTopHomotopy_postcomp η hη r J s x

/-- Every entire original prespectrum homotopy level commutes with precomposition, including
its actual degree-zero based-loop level. -/
lemma prespectrumTransformationHomotopy_precomp_level (J : T ⟶ V) (n : ℕ) :
    (prespectrumTransformationHomotopy (F := J ≫ F) (G := J ≫ G)
      (whiskerLeft J.functor η) (fun A ↦ hη (J.functor.obj A))).level n =
    (Homotopy.precomp (prespectrumMap J) (prespectrumTransformationHomotopy η hη)).level n := by
  cases n with
  | zero =>
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    apply Path.ext
    funext q
    change Path (stagePoint 0 T) (stagePoint 0 T) at x
    exact stageTransformationTopHomotopy_precomp η hη 0 J s (x q)
  | succ r =>
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    exact stageTransformationTopHomotopy_precomp η hη r J s x

/-- At every original homotopy time, postwhiskering gives the literal composed prespectrum map. -/
lemma prespectrumTransformationHomotopy_postcomp_at (J : W ⟶ T) (s : unitInterval) :
    (prespectrumTransformationHomotopy (F := F ≫ J) (G := G ≫ J)
      (whiskerRight η J.functor) (fun A ↦ J.exact.weak _ (hη A))).at s =
    (prespectrumTransformationHomotopy η hη).at s ≫ prespectrumMap J := by
  apply LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun k ↦ k (s, x)) (prespectrumTransformationHomotopy_postcomp_level η hη J n)

/-- At every original homotopy time, prewhiskering gives the literal composed prespectrum map. -/
lemma prespectrumTransformationHomotopy_precomp_at (J : T ⟶ V) (s : unitInterval) :
    (prespectrumTransformationHomotopy (F := J ≫ F) (G := J ≫ G)
      (whiskerLeft J.functor η) (fun A ↦ hη (J.functor.obj A))).at s =
    prespectrumMap J ≫ (prespectrumTransformationHomotopy η hη).at s := by
  apply LoopPrespectrum.Hom.ext
  funext n
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun k ↦ k (s, x)) (prespectrumTransformationHomotopy_precomp_level η hη J n)

end Quillen.Waldhausen.IteratedS
