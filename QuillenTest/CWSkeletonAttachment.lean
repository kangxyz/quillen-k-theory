/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.CWComplex.SkeletonExtension

/-! # Named tests of actual classical-CW skeleton attachment -/
@[expose] public section

open Topology

open Quillen.ClassicalCW

noncomputable section
open Set Metric
universe u v
namespace QuillenTest.CWSkeletonAttachment

open Quillen
open ClassicalCW
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C]

/-- The induction starts with the literal empty previous skeleton. -/
theorem emptyInitialSkeleton : IsEmpty (SkeletonLT C 0) := skeletonLT_zero_isEmpty C

/-- Zero-dimensional cells are covered without a positive-dimensional premise. -/
theorem zeroStepSurjective : Function.Surjective (skeletonStepMap C 0) :=
  skeletonStepMap_surjective C 0

/-- The displayed map is a proved quotient, not supplied attachment data. -/
theorem originalStepQuotient (n : ℕ) : IsQuotientMap (skeletonStepMap C n) :=
  isQuotientMap_skeletonStepMap C n

/-- The original point of every characteristic disk is unchanged. -/
theorem originalCharacteristicValue (n : ℕ) (i : RelCWComplex.cell C n)
    (z : CharacteristicDisk n) :
    (skeletonCharacteristicMap C n i z).val = RelCWComplex.map n i z := rfl

/-- The full original sphere map commutes with the two literal inclusions. -/
theorem literalBoundarySquare (n : ℕ) (i : RelCWComplex.cell C n)
    (t : CharacteristicSphere n) :
    skeletonCharacteristicMap C n i (characteristicSphereInclusion n t) =
      skeletonInclusion C n (characteristicBoundaryMap C n i t) :=
  skeletonCharacteristicMap_boundary C n i t

variable (n : ℕ) {Y : Type v} [TopologicalSpace Y]
variable (a : C(SkeletonLT C n, Y))
variable (b : ∀ _ : RelCWComplex.cell C n, C(CharacteristicDisk n, Y))
variable (hab : ∀ i t, b i (characteristicSphereInclusion n t) =
  a (characteristicBoundaryMap C n i t))

include a hab in
/-- Equal singular boundary or interior images are assigned the same value. -/
theorem coincidentCharacteristicValues (i j : RelCWComplex.cell C n)
    (z w : CharacteristicDisk n)
    (h : RelCWComplex.map n i z = RelCWComplex.map n j w) : b i z = b j w :=
  diskValues_eq_of_same_image C n a b hab i j z w h

/-- The constructed extension keeps both sorts of prescribed input literally. -/
theorem bothRestrictions :
    (∀ x, skeletonStepExtension C n a b hab (skeletonInclusion C n x) = a x) ∧
    (∀ i z, skeletonStepExtension C n a b hab (skeletonCharacteristicMap C n i z) = b i z) :=
  ⟨skeletonStepExtension_old C n a b hab, skeletonStepExtension_disk C n a b hab⟩

end QuillenTest.CWSkeletonAttachment
