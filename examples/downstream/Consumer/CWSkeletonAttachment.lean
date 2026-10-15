/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.CWComplex.SkeletonExtension

/-! # Independent clients of the actual one-step extension theorem -/
@[expose] public section

open Topology

open Quillen.ClassicalCW

noncomputable section
open Set
universe u v w
namespace Quillen.Consumer.CWSkeletonAttachment
open ClassicalCW
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C] (n : ℕ)
variable {Y : Type v} [TopologicalSpace Y]
variable (a : C(SkeletonLT C n, Y))
variable (b : ∀ _ : RelCWComplex.cell C n, C(CharacteristicDisk n, Y))
variable (hab : ∀ i t, b i (characteristicSphereInclusion n t) =
  a (characteristicBoundaryMap C n i t))

include hab in
/-- Actual boundary agreement gives the unique continuous map with both
specified restrictions, without any supplied pushout or global map. -/
theorem existsUniqueOriginalExtension :
    ∃! f : C(SkeletonLT C (n + 1), Y),
      (∀ x, f (skeletonInclusion C n x) = a x) ∧
        (∀ i z, f (skeletonCharacteristicMap C n i z) = b i z) := by
  refine ⟨skeletonStepExtension C n a b hab,
    ⟨skeletonStepExtension_old C n a b hab, skeletonStepExtension_disk C n a b hab⟩, ?_⟩
  intro f hf
  exact skeletonStepExtension_unique C n a b hab f hf.1 hf.2

/-- Local lifts glue over the unchanged base map on the actual next skeleton.
The hypotheses are local equalities on old points and disks, not the desired
global lifting conclusion. -/
theorem gluedExtension_liesOver {Z : Type w} [TopologicalSpace Z]
    (p : C(Y, Z)) (d : C(SkeletonLT C (n + 1), Z))
    (ha : ∀ x, p (a x) = d (skeletonInclusion C n x))
    (hb : ∀ i z, p (b i z) = d (skeletonCharacteristicMap C n i z)) :
    p.comp (skeletonStepExtension C n a b hab) = d := by
  ext y
  obtain ⟨x, rfl⟩ := skeletonStepMap_surjective C n y
  cases x with
  | inl x =>
    change p (skeletonStepExtension C n a b hab (skeletonInclusion C n x)) = _
    rw [skeletonStepExtension_old]
    exact ha x
  | inr z =>
    change p (skeletonStepExtension C n a b hab (skeletonCharacteristicMap C n z.1 z.2)) = _
    rw [skeletonStepExtension_disk]
    exact hb z.1 z.2

end Quillen.Consumer.CWSkeletonAttachment
