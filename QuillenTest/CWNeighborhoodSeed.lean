/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CWComplex.RadialCollar
public import Quillen.Topology.CWComplex.CellNeighborhood

/-! # Exact-coordinate and degenerate-dimension neighborhood regressions -/

@[expose] public section
noncomputable section
open Set Metric Topology Quillen.ClassicalCW
open scoped unitInterval
universe u
namespace QuillenTest.CWNeighborhoodSeed

/-- Empty attaching sphere cannot silently create a zero-dimensional collar. -/
theorem zero_collar_empty (V : Set (CharacteristicSphere 0)) : radialCollarSet 0 V = ∅ :=
  radialCollarSet_zero V

/-- Restriction to the literal sphere recovers the original arbitrary direction set. -/
theorem supplied_sphere_set_retained (n : ℕ) (V : Set (CharacteristicSphere n)) :
    (characteristicSphereInclusion n) ⁻¹' radialCollarSet n V = V := by
  ext z
  exact sphere_mem_radialCollarSet n V z

/-- During collar deformation every original radial direction is retained. -/
theorem collar_direction_unchanged (n : ℕ) (V : Set (CharacteristicSphere n))
    (t : I) (z : RadialCollar n V) :
    radialDirection n (collarRadialMap n V (t, z)).val = radialDirection n z.val :=
  radialDirection_annulusRadialMap n t z.val

/-- The actual radial endpoint is the original normalized sphere point. -/
theorem radial_endpoint_exact (n : ℕ) (z : CharacteristicAnnulus n) :
    (annulusRadialMap n (1, z)).val = characteristicSphereInclusion n (radialDirection n z) :=
  congrArg Subtype.val (annulusRadialMap_one n z)

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C]

/-- Other original cell disks cannot acquire interior seed points. -/
theorem different_cell_avoids_seed (n : ℕ) (i j : RelCWComplex.cell C n)
    (hji : j ≠ i) (z : CharacteristicDisk n) :
    skeletonCharacteristicMap C n j z ∉ cellNeighborhoodSet C n i := by
  intro hz
  exact hji ((characteristic_mem_openCell_iff C n i j z).mp hz).1

/-- The complete closed first half of time is stationary in the original complex. -/
theorem seed_preserves_first_half (n : ℕ) (i : RelCWComplex.cell C n)
    (x y : CellNeighborhood C n i) (t : I) (ht : (t : ℝ) ≤ 1 / 2) :
    cellNeighborhoodAmbientContraction C n i x (t, y) = cellNeighborhoodToComplex C n i y :=
  cellNeighborhoodAmbientContraction_stationary C n i x y t ht

/-- At time one every original seed point reaches exactly the prescribed original point. -/
theorem seed_preserves_prescribed_endpoint (n : ℕ) (i : RelCWComplex.cell C n)
    (x y : CellNeighborhood C n i) :
    cellNeighborhoodAmbientContraction C n i x (1, y) = cellNeighborhoodToComplex C n i x :=
  (cellNeighborhoodAmbientContraction C n i x).apply_one y

/-- The zero-cell seed is genuinely open in the first actual skeleton. -/
theorem zero_seed_open (i : RelCWComplex.cell C 0) : IsOpen (cellNeighborhoodSet C 0 i) :=
  isOpen_cellNeighborhoodSet C 0 i

end QuillenTest.CWNeighborhoodSeed
