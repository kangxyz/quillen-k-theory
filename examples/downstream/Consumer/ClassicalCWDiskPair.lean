/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CWComplex.CubeDiskPair

/-!
# Downstream lifting with a prescribed original sphere map

A commutative disk-boundary square is filled in its original characteristic
coordinates, with both identities as equalities of continuous maps.
-/

@[expose] public section
noncomputable section
open Quillen Quillen.ClassicalCW
universe u v
namespace Consumer.ClassicalCWDiskPair

/-- Cubical lifting solves the original disk square, without changing either given map. -/
theorem exists_disk_lift {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : C(E, B)}
    (hp : CubicalSubdivision.BoundaryLifting p) (n : ℕ)
    (a : C(CharacteristicSphere n, E)) (b : C(CharacteristicDisk n, B))
    (hab : p.comp a = b.comp (characteristicSphereInclusion n)) :
    ∃ c : C(CharacteristicDisk n, E),
      c.comp (characteristicSphereInclusion n) = a ∧ p.comp c = b := by
  obtain ⟨c, hc, hp'⟩ := hp.characteristicDisk n a b
    (fun z ↦ ContinuousMap.congr_fun hab z)
  exact ⟨c, ContinuousMap.ext hc, hp'⟩

/-- In dimension zero, the same property yields every original target point. -/
theorem surjective_of_boundaryLifting {E : Type u} {B : Type v}
    [TopologicalSpace E] [TopologicalSpace B] {p : C(E, B)}
    (hp : CubicalSubdivision.BoundaryLifting p) : Function.Surjective p := by
  intro y
  let := characteristicSphere_zero_isEmpty
  let a : C(CharacteristicSphere 0, E) := ⟨isEmptyElim, continuous_of_discreteTopology⟩
  obtain ⟨c, _, hc⟩ := exists_disk_lift hp 0 a (ContinuousMap.const _ y)
    (ContinuousMap.ext (fun z ↦ isEmptyElim z))
  exact ⟨c characteristicDiskZeroUnique.default,
    ContinuousMap.congr_fun hc characteristicDiskZeroUnique.default⟩

end Consumer.ClassicalCWDiskPair
