/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CWComplex.UniverseTransport

/-! # Independent consumer of actual mixed-universe classical CW transport -/

@[expose] public section
noncomputable section
open Set Metric Topology Quillen.ClassicalCW
universe u v
namespace Consumer.CWUniverseTransport
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C]

/-- A point of the original complex suffices to construct the exact lifted
whole-space CW structure needed by mixed-universe applications. -/
@[instance_reducible]
def actualLiftedStructure (c : C) : CWComplex (univ : Set (ULift.{v} C)) :=
  uliftSubtypeCWComplex C c

/-- The client can choose an arbitrary larger universe while retaining all original
closed-disk characteristic values, rather than assuming transport compatibility. -/
theorem original_characteristic_values (c : C) (n : ℕ) (i : RelCWComplex.cell C n)
    (z : Fin n → ℝ) (hz : z ∈ closedBall (0 : Fin n → ℝ) 1) :
    ((actualLiftedStructure.{u, v} C c).map n (ULift.up i) z).down.val =
      RelCWComplex.map n i z := uliftSubtypeCWComplex_map_val.{u, v} C c n i z hz

end Consumer.CWUniverseTransport
