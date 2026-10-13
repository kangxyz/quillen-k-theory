/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CWComplex.UniverseTransport

/-! # Literal classical CW subtype and universe transport regressions -/

@[expose] public section
noncomputable section
open Set Metric Topology Quillen.ClassicalCW
universe u v
namespace QuillenTest.CWUniverseTransport
variable {X : Type u} [TopologicalSpace X]
variable (C : Set X) [CWComplex C] (c : C)

/-- The intrinsic subtype receives a constructed whole-space classical CW structure. -/
theorem intrinsic_structure_exists [T2Space X] (c : C) : Nonempty (CWComplex (univ : Set C)) :=
  ⟨subtypeCWComplex C c⟩

/-- The intrinsic source is the original literal unit open ball. -/
theorem intrinsic_source (n : ℕ) (i : RelCWComplex.cell C n) :
    (subtypeCharacteristicMap C c n i).source = ball (0 : Fin n → ℝ) 1 := rfl

/-- The intrinsic chart keeps every value on the entire closed disk. -/
theorem intrinsic_closed_disk_values (n : ℕ) (i : RelCWComplex.cell C n)
    (z : Fin n → ℝ) (hz : z ∈ closedBall (0 : Fin n → ℝ) 1) :
    (subtypeCharacteristicMap C c n i z).val = RelCWComplex.map n i z :=
  subtypeCharacteristicMap_val C c n i z hz

/-- Original chart targets are simply restricted to the actual subtype. -/
theorem intrinsic_target (n : ℕ) (i : RelCWComplex.cell C n) :
    (subtypeCharacteristicMap C c n i).target =
      Subtype.val ⁻¹' (RelCWComplex.map n i).target := rfl

/-- The irrelevant fallback point cannot change any actual closed-disk value. -/
theorem fallback_independent (d : C) (n : ℕ) (i : RelCWComplex.cell C n)
    (z : Fin n → ℝ) (hz : z ∈ closedBall (0 : Fin n → ℝ) 1) :
    subtypeCharacteristicMap C c n i z = subtypeCharacteristicMap C d n i z := by
  apply Subtype.ext
  rw [subtypeCharacteristicMap_val C c n i z hz, subtypeCharacteristicMap_val C d n i z hz]

variable [T2Space X]

/-- The lifted actual subtype gets a CW structure in the larger universe. -/
theorem lifted_structure_exists (c : C) : Nonempty (CWComplex (univ : Set (ULift.{v} C))) :=
  ⟨uliftSubtypeCWComplex C c⟩

/-- The lifted source remains the same disk source. -/
theorem lifted_source (n : ℕ) (i : RelCWComplex.cell C n) :
    ((uliftSubtypeCWComplex.{u, v} C c).map n (ULift.up i)).source =
      ball (0 : Fin n → ℝ) 1 := uliftSubtypeCWComplex_source.{u, v} C c n i

/-- Both literal projections recover the original closed-disk chart values. -/
theorem lifted_closed_disk_values (n : ℕ) (i : RelCWComplex.cell C n)
    (z : Fin n → ℝ) (hz : z ∈ closedBall (0 : Fin n → ℝ) 1) :
    ((uliftSubtypeCWComplex.{u, v} C c).map n (ULift.up i) z).down.val =
      RelCWComplex.map n i z := uliftSubtypeCWComplex_map_val.{u, v} C c n i z hz

/-- The inverse remains the original inverse after the actual down/subtype maps. -/
theorem lifted_inverse (n : ℕ) (i : RelCWComplex.cell C n) (y : ULift.{v} C) :
    ((uliftSubtypeCWComplex.{u, v} C c).map n (ULift.up i)).symm y =
      (RelCWComplex.map n i).symm y.down.val := uliftSubtypeCWComplex_map_symm.{u, v} C c n i y

/-- The zero-cell case uses the same construction, with no nonempty coordinate index. -/
theorem zero_cell_values (i : RelCWComplex.cell C 0) (z : Fin 0 → ℝ)
    (hz : z ∈ closedBall (0 : Fin 0 → ℝ) 1) :
    ((uliftSubtypeCWComplex.{u, v} C c).map 0 (ULift.up i) z).down.val =
      RelCWComplex.map 0 i z := uliftSubtypeCWComplex_map_val.{u, v} C c 0 i z hz

end QuillenTest.CWUniverseTransport
