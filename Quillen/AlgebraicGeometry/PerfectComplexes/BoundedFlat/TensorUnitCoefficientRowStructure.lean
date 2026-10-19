/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientStageRealization
public import Quillen.Waldhausen.SConstruction.Iterated.RowCylinderRealization

/-!
# The actual first coefficient row and the next spectrum structure direction

The independently realized tensor coefficient cell has a whole three-parameter structure
identity. The coefficient row, forward unit edge, and next structure interval remain separate.
The identity retains the actual row transpose; it does not silently identify it with the identity
or assert compatibility of inverse-prefix normalization with the ordinary looped tail.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (r : (Γ(X, ⊤))ˣ)

/-- The genuine first-row cell commutes with the next structure interval after its actual swap. -/
theorem tensorUnitPullbackCoefficientStageRealization_row_structure
    (k : ℕ) (s t a : unitInterval)
    (x : stageSpace k (modelOf (boundedFlatPerfectWaldhausen Y))) :
    stageRowSwapHomeomorph k (modelOf (boundedFlatPerfectWaldhausen X))
      (tensorUnitPullbackCoefficientStageRealization f r (k + 1)
        (s, (t, stageLoopMap k (modelOf (boundedFlatPerfectWaldhausen Y)) x a))) =
      stageLoopMap (k + 1) (modelOf (boundedFlatPerfectWaldhausen X))
        (tensorUnitPullbackCoefficientStageRealization f r k (s, (t, x))) a := by
  rw [tensorUnitPullbackCoefficientStageRealization_structure,
    tensorUnitPullbackCoefficientStageRealization_structure]
  erw [(boundedFlatPerfectTensorUnitHomotopy f r).comm (k + 1) t x a]
  exact stageLoopMap_rowSwap k (modelOf (boundedFlatPerfectWaldhausen X))
    ((boundedFlatPerfectTensorUnitHomotopy f r).level (k + 1) (t, x)) a s

end Quillen.PerfectComplexes
