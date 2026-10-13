/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricOrderComplex.RealizationHomotopyEquiv
public import Quillen.Topology.HomotopyEquiv.BasedLoop

/-!
# Actual compact-open loops of the weak/strong order-complex comparison

The independent client loops the displayed vertex-fixed homotopy equivalence.
Its forward map is pointwise the original realization coordinate map; its
inverse is pointwise the normalized half-maximum cutoff reconstruction.
The inverse homotopies retain constant loops in the actual Path topology.
-/

@[expose] public section
noncomputable section

open CategoryTheory Quillen Quillen.MetricOrderComplex
open scoped Simplicial Topology unitInterval

universe u
namespace Consumer.MetricOrderHomotopyEquiv

variable {P : Type u} [PartialOrder P]

/-- A genuine homotopy equivalence of the original compact-open based loop spaces. -/
def loopComparison (p : P) :
    ContinuousMap.HomotopyEquiv
      (Path (classifyingSpacePoint.{u, u} p) (classifyingSpacePoint.{u, u} p))
      (Path (vertex p) (vertex p)) :=
  (basedRealizationHomotopyEquiv p).loopHomotopyEquiv

/-- No path-space replacement changes the actual forward loop map. -/
theorem loopComparison_apply (p : P)
    (γ : Path (classifyingSpacePoint.{u, u} p) (classifyingSpacePoint.{u, u} p)) (t : I) :
    loopComparison p γ t = realizationCoordinates (γ t) := rfl

/-- The reverse loop map is the actual cutoff reconstruction at every time. -/
theorem loopComparison_inv_apply (p : P) (γ : Path (vertex p) (vertex p)) (t : I) :
    (loopComparison p).invFun γ t = cutoffRealizationMap (γ t) := rfl

/-- The displayed weak-side loop homotopy retains the original constant loop. -/
theorem left_homotopy_refl (p : P) (t : I) :
    (basedRealizationHomotopyEquiv p).loopLeftHomotopy
      (t, Path.refl (classifyingSpacePoint.{u, u} p)) =
        Path.refl (classifyingSpacePoint.{u, u} p) :=
  (basedRealizationHomotopyEquiv p).loopLeftHomotopy_refl t

/-- The displayed metric-side loop homotopy retains the original constant loop. -/
theorem right_homotopy_refl (p : P) (t : I) :
    (basedRealizationHomotopyEquiv p).loopRightHomotopy (t, Path.refl (vertex p)) =
      Path.refl (vertex p) :=
  (basedRealizationHomotopyEquiv p).loopRightHomotopy_refl t

-- This applies without a countability or local-finiteness hypothesis on the poset.
example (p : Set ℝ) :
    ContinuousMap.HomotopyEquiv
      (Path (classifyingSpacePoint p) (classifyingSpacePoint p))
      (Path (vertex p) (vertex p)) := loopComparison p

end Consumer.MetricOrderHomotopyEquiv
