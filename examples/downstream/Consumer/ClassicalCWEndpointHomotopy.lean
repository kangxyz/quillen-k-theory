/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyPullback.PathProjectionLifting
public import Quillen.Topology.CWComplex.GlobalLifting

/-!
# Exact prescribed-endpoint homotopies over an original classical CW subtype

The generic two-endpoint path projection is lifted by the separately constructed
global CW lift. Compact-open uncurrying provides joint continuity without
assuming a CW structure on a product or converting between CW notions.
-/

@[expose] public section

open Topology
noncomputable section
open Quillen Quillen.HomotopyPullback
open Set
open scoped unitInterval
universe u v
namespace Consumer.ClassicalCWEndpointHomotopy
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C]
variable {E B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable (p : C(E, B)) (hp : CubicalSubdivision.BoundaryLifting p)

/-- A homotopy downstairs has a jointly continuous lift with both given endpoint maps. -/
def liftedHomotopy (a₀ a₁ : C(C, E))
    (H : (p.comp a₀).Homotopy (p.comp a₁)) : a₀.Homotopy a₁ :=
  homotopyOfPathProjectionLift p a₀ a₁ H
    (ClassicalCW.globalLift C (pathProjection p) hp.pathProjection (homotopyTarget p a₀ a₁ H))
    (ClassicalCW.globalLift_comp C (pathProjection p) hp.pathProjection
      (homotopyTarget p a₀ a₁ H))

/-- Projection keeps the given base homotopy pointwise for every time and original point. -/
theorem liftedHomotopy_project (a₀ a₁ : C(C, E))
    (H : (p.comp a₀).Homotopy (p.comp a₁)) (t : I) (x : C) :
    p (liftedHomotopy C p hp a₀ a₁ H (t, x)) = H (t, x) :=
  homotopyOfPathProjectionLift_project p a₀ a₁ H _ _ t x

end Consumer.ClassicalCWEndpointHomotopy
