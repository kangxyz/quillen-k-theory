/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.DiagramRowNormalizedBoundaryNaturality

/-! Independent-time regressions for the whole normalized boundary prism. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen Quillen.LoopPrespectrum Quillen.KTheory.Bass
open scoped Topology unitInterval
universe u v w
namespace QuillenTest.DiagramRowNormalizedBoundaryNaturality
open DiagramRowSeed
variable {C : Type u} [Category.{v} C] (Q : C ⥤ Arrow (Arrow C))
  {F G : C ⥤ LoopPrespectrum.{w}}
  (qF : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hpF : ∀ X k, qF X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hnF : ∀ {X Y} (g : X ⟶ Y) k x,
    qF Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (qF X k x))
  (qG : ∀ X k, C((G.obj X).space (k + 3), (G.obj X).space (k + 3)))
  (hpG : ∀ X k, qG X k ((G.obj X).point (k + 3)) = (G.obj X).point (k + 3))
  (hnG : ∀ {X Y} (g : X ⟶ Y) k x,
    qG Y k ((G.map g).map (k + 3) x) = (G.map g).map (k + 3) (qG X k x))
  (hsF : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
    qF X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
      (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)
  (hsG : ∀ X k (x : (G.obj X).space (k + 1)) (s t : unitInterval),
    qG X k ((G.obj X).structureMap (k + 2) ((G.obj X).structureMap (k + 1) x s) t) =
      (G.obj X).structureMap (k + 2) ((G.obj X).structureMap (k + 1) x t) s)
  (η : F ⟶ G)
  (hη : ∀ X k x, qG X k ((η.app X).map (k + 3) x) =
    (η.app X).map (k + 3) (qF X k x))


variable (X : C)
  (KF : Homotopy (diagonal Q F X ≫ cornerComparison Q F qF hpF hsF X)
    (diagonal Q F X ≫ cornerComparison Q F qF hpF hsF X))
  (KG : Homotopy (diagonal Q G X ≫ cornerComparison Q G qG hpG hsG X)
    (diagonal Q G X ≫ cornerComparison Q G qG hpG hsG X))
  (hK : ∀ n t x, (cornerRowMap Q qF hpF qG hpG η hη X).map n
    (KF.level n (t, x)) = KG.level n (t, (η.app (Q.obj X).left.left).map n x))


include hK

/-- Positive levels retain normalization, output-loop, and original row times independently. -/
theorem positive_times (k : ℕ) (s t r : unitInterval)
    (x : (F.obj (Q.obj X).left.left).space (k + 1)) :
    ((ConeTrack.map Q η).app X).map (k + 2)
      (Path.toContinuousMap (Path.toContinuousMap
        ((normalizedBoundaryHomotopy Q F qF hpF hnF hsF X KF).level (k + 1) (s, x)) t) r) =
    Path.toContinuousMap (Path.toContinuousMap
      ((normalizedBoundaryHomotopy Q G qG hpG hnG hsG X KG).level (k + 1)
        (s, (η.app (Q.obj X).left.left).map (k + 1) x)) t) r :=
  congrArg (fun p => Path.toContinuousMap (Path.toContinuousMap p t) r)
    (normalizedBoundaryHomotopy_naturality_apply Q qF hpF hnF qG hpG hnG hsF hsG
      η hη X KF KG hK (k + 1) s x)

/-- Degree zero also retains the independent source-loop coordinate. -/
theorem zero_times (s t r v : unitInterval)
    (x : (F.obj (Q.obj X).left.left).space 0) :
    ((ConeTrack.map Q η).app X).map 2
      (Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap
        ((normalizedBoundaryHomotopy Q F qF hpF hnF hsF X KF).level 0 (s, x)) t) r) v) =
    Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap
      ((normalizedBoundaryHomotopy Q G qG hpG hnG hsG X KG).level 0
        (s, (η.app (Q.obj X).left.left).map 0 x)) t) r) v :=
  congrArg (fun p => Path.toContinuousMap (Path.toContinuousMap (Path.toContinuousMap p t) r) v)
    (normalizedBoundaryHomotopy_naturality_apply Q qF hpF hnF qG hpG hnG hsF hsG
      η hη X KF KG hK 0 s x)

end QuillenTest.DiagramRowNormalizedBoundaryNaturality
