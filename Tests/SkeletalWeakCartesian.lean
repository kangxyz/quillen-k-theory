/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.TheoremB.SkeletalWeakCartesianInduction

/-!
# Original weak-cartesian skeletal comparisons

These consumers retain two arbitrary coefficient diagrams, actual transition
squares, empty skeletons, degenerate characteristic charts, and the full original
constant-path comparison at finite stages and in the sequential colimit.
-/
@[expose] public section

noncomputable section
open CategoryTheory Limits Opposite Quillen Quillen.TheoremA Quillen.TheoremB
open Quillen.CartesianRealization.Skeletal
open scoped Simplicial Topology unitInterval
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D : Type u} [SmallCategory D] {H J : D ⥤ SSet.{u}} (η : H ⟶ J)

example : StageWeakCharts η 0 := stageWeakCharts_zero η
example (htrans : TransitionWeakCartesian η) (n : ℕ) : StageWeakCharts η n :=
  stageWeakCharts η htrans n
example (htrans : TransitionWeakCartesian η) (k n : ℕ) (h : k ≤ n) :
    IsWeakHomotopyEquivalence
      (Quillen.CartesianRealization.Sequential.stageComparison (realizedReplacementSkeletonMap η) k n h) :=
  stageComparison_isWeakHomotopyEquivalence η htrans k n h
example (htrans : TransitionWeakCartesian η) (k : ℕ) :
    IsWeakHomotopyEquivalence (replacementSkeletonComparison η k) :=
  Quillen.CartesianRealization.Skeletal.replacementSkeletonComparison_isWeakHomotopyEquivalence η htrans k
example (htrans : TransitionWeakCartesian η) :
    FiniteCubeStrictHELP (replacementSkeletonComparison η 0) :=
  (Quillen.CartesianRealization.Skeletal.replacementSkeletonComparison_isWeakHomotopyEquivalence η htrans
    0).cube_strictHELP
example (n : ℕ) : WeakCartesian (cellBoundaryProjection η n).hom (cellProjection η n).hom
    (boundaryLeg H n).hom (boundaryLeg J n).hom
    (congrArg TopCat.Hom.hom (cellBoundarySquare η n)) :=
  replacementBoundary_weakCartesian η n
example (htrans : TransitionWeakCartesian η) (n : ℕ) :
    WeakCartesian (cellBoundaryProjection η n).hom (stageProjection η n).hom
      (attachingLeg H n).hom (attachingLeg J n).hom
      (congrArg TopCat.Hom.hom (cellAttachingSquare η n)) :=
  replacementAttaching_weakCartesian η htrans n (stageWeakCharts η htrans n)
example (A : (nerve D).Subcomplex) {n k : ℕ}
    (s : (nerve D).obj (op ⦋k⦌)) (hs : s ∈ A.obj (op ⦋k⦌))
    (α : ⦋n⦌ ⟶ ⦋k⦌) [Epi α] (h : ChartWeakCartesian η A s hs) :
    ChartWeakCartesian η A ((nerve D).map α.op s) (A.map α.op hs) :=
  ChartWeakCartesian.of_epi η A s hs α h
example (k n : ℕ) (h : k ≤ n) (x : (realizedReplacementSkeleton H).obj k) (t : unitInterval) :
    (Quillen.CartesianRealization.Sequential.stageComparison (realizedReplacementSkeletonMap η) k n h x).val.2.2 t =
      (realizedReplacementSkeleton J).map (homOfLE h) ((realizedReplacementSkeletonMap η).app k x)
        := rfl
example (k : ℕ) (x : (realizedReplacementSkeleton H).obj k) (t : unitInterval) :
    (replacementSkeletonComparison η k x).val.2.2 t =
      (realizedReplacementSkeletonCocone J).ι.app k ((realizedReplacementSkeletonMap η).app k x) :=
        rfl
example (k : ℕ) (x : (realizedReplacementSkeleton H).obj k) :
    (replacementSkeletonComparison η k x).val.2.1 =
      (realizedReplacementSkeletonCocone H).ι.app k x := rfl
example (k : ℕ) (x : (realizedReplacementSkeleton H).obj k) :
    (replacementSkeletonComparison η k x).val.1 = (realizedReplacementSkeletonMap η).app k x := rfl
