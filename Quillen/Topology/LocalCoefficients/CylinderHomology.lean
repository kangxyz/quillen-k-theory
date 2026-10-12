/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.HomotopyEquivalence
public import Mathlib.Topology.UnitInterval

/-! # Original cylinder projection and endpoint maps with local coefficients -/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped unitInterval
universe u
namespace Quillen.LocalCoefficients
variable (X : Type u) [TopologicalSpace X]

/-- The actual projection from the closed interval cylinder. -/
def cylinderProjection : C(unitInterval × X, X) := ⟨Prod.snd, continuous_snd⟩

/-- The actual inclusion at the prescribed interval coordinate. -/
def cylinderSection (t : unitInterval) : C(X, unitInterval × X) :=
  ⟨fun x => (t, x), by fun_prop⟩

/-- Contraction to any specified cylinder slice, retaining the original projection. -/
def cylinderProjectionEquiv (t : unitInterval) :
    ContinuousMap.HomotopyEquiv (unitInterval × X) X where
  toFun := cylinderProjection X
  invFun := cylinderSection X t
  left_inv := ⟨{
    toFun := fun z => (Set.Icc.convexComb t z.2.1 z.1, z.2.2)
    continuous_toFun := by fun_prop
    map_zero_left := by intro z; simp [cylinderProjection, cylinderSection]
    map_one_left := by intro z; simp }⟩
  right_inv := by
    have h : (cylinderProjection X).comp (cylinderSection X t) = ContinuousMap.id X := rfl
    rw [h]

/-- Every genuine target local system is preserved by the original cylinder projection. -/
theorem cylinderProjection_homology_isIso (A : System.{u, u} X) (n : ℕ) :
    IsIso (pushforwardHomologyMap (cylinderProjection X) A n) :=
  isIso_pushforwardHomologyMap_of_homotopyEquiv (cylinderProjectionEquiv X 0) A n

/-- Every cylinder slice inclusion preserves arbitrary local systems on the cylinder. -/
theorem cylinderSection_homology_isIso (t : unitInterval)
    (A : System.{u, u} (unitInterval × X)) (n : ℕ) :
    IsIso (pushforwardHomologyMap (cylinderSection X t) A n) :=
  isIso_pushforwardHomologyMap_of_homotopyEquiv (cylinderProjectionEquiv X t).symm A n

end Quillen.LocalCoefficients
