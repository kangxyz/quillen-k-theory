/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.CWComplex.GlobalLifting

/-! # Named tests of genuine global classical-CW lifting -/
@[expose] public section
noncomputable section
open Set Topology
universe u v w
namespace QuillenTest.CWGlobalLifting

open Quillen
open ClassicalCW
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C]
variable {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]
variable (p : C(E, B)) (hp : CubicalSubdivision.BoundaryLifting p) (f : C(C, B))

/-- The induction has a zero stage even without an inhabitant of the total space. -/
theorem initialStageExists : Nonempty (SkeletonLiftAt C p f 0) :=
  ⟨initialSkeletonLift C p f⟩

/-- Successive maps retain the old skeleton pointwise. -/
theorem adjacentStageAgreement (n : ℕ) (x : SkeletonLT C n) :
    (skeletonLiftFamily C p hp f (n + 1)).val (skeletonInclusion C n x) =
      (skeletonLiftFamily C p hp f n).val x :=
  skeletonLiftFamily_succ C p hp f n x

/-- Arbitrarily separated stages give the same value to the original point. -/
theorem distantStageAgreement {n m : ℕ} (h : n ≤ m) (x : SkeletonLT C n) :
    (skeletonLiftFamily C p hp f m).val (skeletonInclusionLE C h x) =
      (skeletonLiftFamily C p hp f n).val x :=
  skeletonLiftFamily_compatible C p hp f h x

/-- The actual global map satisfies the unchanged original map equation. -/
theorem strictGlobalEquation : p.comp (globalLift C p hp f) = f :=
  globalLift_comp C p hp f

/-- The global map uses the stored continuous map on every original disk. -/
theorem originalDiskRestriction (n : ℕ) (i : RelCWComplex.cell C n)
    (z : CharacteristicDisk n) :
    globalLift C p hp f (characteristicQuotient C ⟨n, i, z⟩) =
      (skeletonLiftFamily C p hp f (n + 1)).val (skeletonCharacteristicMap C n i z) :=
  globalLift_on_skeleton C p hp f (n + 1) (skeletonCharacteristicMap C n i z)

include hp f in
/-- A point of the CW domain yields a point upstairs; no nonemptiness premise was hidden. -/
theorem totalSpaceNonempty (x : C) : Nonempty E := ⟨globalLift C p hp f x⟩

end QuillenTest.CWGlobalLifting
