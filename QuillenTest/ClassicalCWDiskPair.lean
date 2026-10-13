/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CWComplex.CubeDiskPair

/-! # Original-coordinate and zero-dimensional disk-pair regressions -/
@[expose] public section
noncomputable section
open Quillen Quillen.ClassicalCW
open scoped unitInterval
universe u v

namespace QuillenTest.ClassicalCWDiskPair

/-- Every zero-dimensional map to the base has a disk lift; the boundary condition is vacuous. -/
theorem zero_disk_lift {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : C(E, B)} (hp : CubicalSubdivision.BoundaryLifting p)
    (b : C(CharacteristicDisk 0, B)) : ∃ c : C(CharacteristicDisk 0, E), p.comp c = b := by
  let := characteristicSphere_zero_isEmpty
  obtain ⟨c, _, hc⟩ := hp.characteristicDisk 0
    (⟨isEmptyElim, continuous_of_discreteTopology⟩ : C(CharacteristicSphere 0, E)) b
    (fun z ↦ isEmptyElim z)
  exact ⟨c, hc⟩

/-- The left endpoint of the one-cube maps to the actual negative unit sphere point. -/
theorem left_endpoint_coordinate :
    (cubeDiskHomeomorph 1 (fun _ ↦ 0)).val 0 = -1 := by simp

/-- The right endpoint of the one-cube maps to the actual positive unit sphere point. -/
theorem right_endpoint_coordinate :
    (cubeDiskHomeomorph 1 (fun _ ↦ 1)).val 0 = 1 := by norm_num

/-- Every sphere point is recovered with its original ambient disk coordinates. -/
theorem sphere_coordinates_recovered (n : ℕ) (z : CharacteristicSphere n) :
    (cubeDiskHomeomorph n ((cubeBoundarySphereHomeomorph n).symm z).val).val = z.val := by
  rw [cubeBoundarySphereHomeomorph_symm_val, Homeomorph.apply_symm_apply]
  rfl

/-- A prescribed sphere lift is preserved at each sphere point after transportation. -/
theorem prescribed_sphere_lift {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : C(E, B)}
    (hp : CubicalSubdivision.BoundaryLifting p) (n : ℕ)
    (a : C(CharacteristicSphere n, E)) (b : C(CharacteristicDisk n, B))
    (hab : ∀ z, p (a z) = b (characteristicSphereInclusion n z)) :
    ∃ c : C(CharacteristicDisk n, E),
      c.comp (characteristicSphereInclusion n) = a ∧ p.comp c = b := by
  obtain ⟨c, hc, hp'⟩ := hp.characteristicDisk n a b hab
  exact ⟨c, ContinuousMap.ext hc, hp'⟩

end QuillenTest.ClassicalCWDiskPair
