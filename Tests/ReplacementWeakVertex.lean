/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.CategoryTheory.TheoremB.ReplacementWeakVertex

/-! # Original replacement vertex consumers

The source and both coordinates are the original realized maps. The comparisons
retain the full path and complete finite relative lifting, including components.
-/
noncomputable section
open CategoryTheory Limits Opposite Quillen Quillen.TheoremA Quillen.TheoremB
open Quillen.TheoremB.SkeletalCartesian
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D : Type u} [SmallCategory D] {H J : D ⥤ SSet.{u}} (η : H ⟶ J)

example (d : D) : Cartesian (SSet.toTop.map (η.app d)).hom
    ((realizedReplacementSkeletonMap η).app 1).hom
    (replacementStageOneVertexMap H d) (replacementStageOneVertexMap J d)
    (replacementStageOneVertex_square η d) :=
  replacementStageOneVertex_cartesian η d

example (h : TransitionWeakCartesian η) (d : D) :
    IsWeakHomotopyEquivalence (HomotopyPullback.comparison
      (SSet.toTop.map (diagonalMap (simplicialReplacementMap η))).hom
      (SSet.toTop.map (replacementVertexInclusion J d)).hom
      (SSet.toTop.map (η.app d)).hom
      (SSet.toTop.map (replacementVertexInclusion H d)).hom
      (replacementVertex_square η d)) :=
  replacementVertexComparison_isWeakHomotopyEquivalence η h d

example (h : TransitionWeakCartesian η) (d : D) :
    FiniteCubeStrictHELP (HomotopyPullback.comparison
      (SSet.toTop.map (diagonalMap (simplicialReplacementMap η))).hom
      (SSet.toTop.map (replacementVertexInclusion J d)).hom
      (SSet.toTop.map (η.app d)).hom
      (SSet.toTop.map (replacementVertexInclusion H d)).hom
      (replacementVertex_square η d)) :=
  (replacementVertexComparison_isWeakHomotopyEquivalence η h d).cube_strictHELP

example (d : D) (x : |H.obj d|) (t : unitInterval) :
    (HomotopyPullback.comparison _ _ _ _ (replacementVertex_square η d) x).val.2.2 t =
      SSet.toTop.map (replacementVertexInclusion J d) (SSet.toTop.map (η.app d) x) := rfl

example (d : D) (x : |H.obj d|) :
    (HomotopyPullback.comparison _ _ _ _ (replacementVertex_square η d) x).val.2.1 =
      SSet.toTop.map (replacementVertexInclusion H d) x := rfl

example (d : D) (x : |H.obj d|) :
    (HomotopyPullback.comparison _ _ _ _ (replacementVertex_square η d) x).val.1 =
      SSet.toTop.map (η.app d) x := rfl

example (d : D) (x : |H.obj d|) :
    (realizedReplacementSkeletonCocone H).ι.app 1 (replacementStageOneVertexMap H d x) =
      SSet.toTop.map (replacementVertexInclusion H d) x :=
  realizedReplacementStageOneHomeomorph_colimit H d x
