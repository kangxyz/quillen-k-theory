/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.HomotopyCofiber.ReducedMappingConeFiberReduction
public import Quillen.Topology.DoubleMappingCylinder.GapConnectivity

/-!
# Finite excision for the literal reduced cone-to-fiber comparison

The original double-cylinder theorem applies to the ordinary cone with its singleton endpoint.
Removing that singleton preserves the complete cylinder path. The genuine chosen-point collapse
then yields the same finite range for the actual reduced cone comparison under original point HEP.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology
universe u
namespace Quillen.ReducedMappingCone
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y))

/-- Removing the singleton endpoint identifies the original cylinder target with its fiber. -/
def unreducedGapFiberHomeomorph :
    HomotopyPullback (DoubleCylinder.gapLeftEndpoint (B := TopCat.of Y) (C := TopCat.of PUnit)
      (unreducedEnd f))
      (DoubleCylinder.gapRightEndpoint (B := TopCat.of Y) (C := TopCat.of PUnit)
      (unreducedEnd f)) ≃ₜ
        HomotopyFiber (unreducedInclusion f) (unreducedVertex f) :=
  HomotopyFiber.singletonParameterHomeomorph (unreducedInclusion f) PUnit
    (DoubleCylinder.gapRightEndpoint (B := TopCat.of Y) (C := TopCat.of PUnit)
      (unreducedEnd f)) PUnit.unit

/-- The entire original unreduced cylinder is retained by the singleton comparison. -/
theorem unreducedGapFiberHomeomorph_comp_gap :
    (unreducedGapFiberHomeomorph f).toHomotopyEquiv.toFun.comp
      (DoubleCylinder.gap (TopCat.ofHom f)
        (TopCat.ofHom (ContinuousMap.const X PUnit.unit)) (unreducedSquare f)) =
          unreducedFiberComparison f := rfl

/-- Finite excision for the actual ordinary cone-to-inclusion-fiber comparison. -/
theorem unreducedFiberComparison_isHomotopyConnectedMap (p q r : ℕ)
    (hr : r + 1 ≤ p + q) (hf : IsHomotopyConnectedMap f p)
    (hX : IsHomotopyConnectedMap (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})) q) :
    IsHomotopyConnectedMap (unreducedFiberComparison f) r :=
  IsHomotopyConnectedMap.of_equivalence_square (ContinuousMap.HomotopyEquiv.refl X)
    (unreducedGapFiberHomeomorph f).toHomotopyEquiv
    (unreducedGapFiberHomeomorph_comp_gap f) r
    (DoubleCylinder.gap_isHomotopyConnectedMap (TopCat.ofHom f)
      (TopCat.ofHom (ContinuousMap.const X PUnit.unit)) (unreducedSquare f) p q r hr hf hX)

/-- Finite excision for the unchanged reduced cone gap, with explicit original point HEP. -/
theorem fiberComparison_isHomotopyConnectedMap (x₀ : X) (y₀ : Y) (hf : f x₀ = y₀)
    (hX : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} x₀)))
    (hY : Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} y₀)))
    (p q r : ℕ) (hr : r + 1 ≤ p + q) (hfp : IsHomotopyConnectedMap f p)
    (hXq : IsHomotopyConnectedMap (ContinuousMap.const X (PUnit.unit : PUnit.{u + 1})) q) :
    IsHomotopyConnectedMap (fiberComparison x₀ y₀ f) r :=
  fiberComparison_isHomotopyConnectedMap_of_unreduced x₀ y₀ f hf hX hY r
    (unreducedFiberComparison_isHomotopyConnectedMap f p q r hr hfp hXq)

end Quillen.ReducedMappingCone
