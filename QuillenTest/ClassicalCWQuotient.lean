/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CWComplex.CharacteristicQuotient

/-! Named regressions on the literal classical-CW characteristic quotient. -/
@[expose] public section
noncomputable section
open Set Metric Topology
open scoped unitInterval
universe u v
namespace QuillenTest.ClassicalCWQuotient
open Quillen.ClassicalCW
variable {X : Type u} [TopologicalSpace X] (C : Set X) [CWComplex C]

/-- The quotient evaluates to the original Mathlib characteristic map. -/
theorem literal_characteristic_value (n : ℕ) (i : RelCWComplex.cell C n)
    (z : CharacteristicDisk n) :
    (characteristicQuotient C ⟨n, i, z⟩).val = RelCWComplex.map n i z := rfl

/-- Dimension zero uses the actual zero-dimensional closed disk. -/
theorem zero_dimensional_value (i : RelCWComplex.cell C 0) :
    (characteristicQuotient C ⟨0, i, ⟨0, by simp⟩⟩).val =
      RelCWComplex.map 0 i 0 := rfl

/-- Agreement on every original disk detects equality on the actual CW subtype. -/
theorem diskwise_equality {Y : Type v} (f g : C → Y)
    (h : ∀ n (i : RelCWComplex.cell C n) (z : CharacteristicDisk n),
      f (characteristicQuotient C ⟨n, i, z⟩) =
        g (characteristicQuotient C ⟨n, i, z⟩)) : f = g := by
  funext x
  obtain ⟨⟨n, i, z⟩, rfl⟩ := characteristicQuotient_surjective C x
  exact h n i z

variable [T2Space X]

/-- Closed subsets of the actual subtype are exactly those with closed disk-sum preimage. -/
theorem literal_closed_preimage (S : Set C) :
    IsClosed S ↔ IsClosed (characteristicQuotient C ⁻¹' S) :=
  (isQuotientMap_iff_isClosed.mp (isQuotientMap_characteristicQuotient C)).2 S

/-- Maps into an unrelated target universe are determined continuously by the disks. -/
theorem cellwise_continuity {Y : Type v} [TopologicalSpace Y] (f : C → Y)
    (h : ∀ n (i : RelCWComplex.cell C n),
      Continuous (fun z : CharacteristicDisk n => f (characteristicQuotient C ⟨n, i, z⟩))) :
    Continuous f := (continuous_iff_characteristic C f).mpr h

/-- Actual path components of the CW subtype are open. -/
theorem open_actual_path_component (x : C) : IsOpen (pathComponent x) := by
  let := Quillen.ClassicalCW.locallyPathConnectedSpace C
  exact IsOpen.pathComponent x

end QuillenTest.ClassicalCWQuotient
