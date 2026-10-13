/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.DoubleMappingCylinder.Connectivity
public import Quillen.Topology.HomotopyCofiber.ReducedMappingConeCollapse
public import Quillen.Topology.HomotopyGroups.Contractible

/-!
# Finite vanishing of the original reduced mapping cone

The point-corner double cylinder preserves finite vanishing above the explicit cutoff two.
Genuine HEP at the two specified original points transfers this through the actual reduction
homotopy equivalence. Every point of the original quotient cone is retained.
-/
@[expose] public section
noncomputable section
universe u
namespace Quillen.ReducedMappingCone
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

/-- Original point HEP and finite source/target vanishing imply the same bound on the actual cone.
-/
theorem homotopyGroup_subsingleton (x₀ : X) (y₀ : Y) (f : C(X, Y)) (hf : f x₀ = y₀)
    (hX : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x₀)))
    (hY : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} y₀)))
    (n : ℕ)
    (hπX : ∀ x k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k X x))
    (hπY : ∀ y k, k < n + 2 → Subsingleton (HomotopyGroup.Pi k Y y))
    (z : Space x₀ y₀ f) (k : ℕ) (hk : k < n + 2) :
    Subsingleton (HomotopyGroup.Pi k (Space x₀ y₀ f) z) := by
  let e := (reductionHomotopyEquiv x₀ y₀ f hf hX hY).symm
  let := DoubleCylinder.homotopyGroup_subsingleton (TopCat.ofHom f)
    (TopCat.ofHom (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})))
    (unreducedSquare f) x₀ n hπX hπY
    (fun p j _ ↦ subsingleton_pi_of_contractible j PUnit.{u + 1} p) (e z) k hk
  exact (homotopyGroupMap_bijective_of_homotopyEquiv e rfl k).injective.subsingleton

end Quillen.ReducedMappingCone
