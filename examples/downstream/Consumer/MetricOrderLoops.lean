/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricOrderComplex.LoopEquiconnection
public import Quillen.Topology.MetricOrderComplex.RealizationHomotopyEquiv
public import Quillen.Topology.ClassifyingSpace.PosetLoop
public import Quillen.Algebra.Category.ModuleCat.FiniteProjective
public import Quillen.CategoryTheory.QConstruction.Connected

/-!
# Actual metric and equi-locally convex loop geometry for the original Q target

Compose the genuine G2 compact-open loop equivalence with the already-proved
poset-resolution loop equivalence of the original finite-projective Q category.
The source is a literal based Path space with the compatible sup metric and
proved open connector-convex neighborhoods. The original constant loop and
pointwise forward map are retained exactly. No original completion comparison,
loop-space realization domination, or CW-type upgrade is assumed here.
-/

@[expose] public section
noncomputable section

open CategoryTheory Quillen Quillen.MetricOrderComplex Quillen.RankedChainOrder
open scoped Topology unitInterval ZeroObject

universe u
namespace Consumer.MetricOrderLoops

variable (R : Type u) [Ring R]

/-- The canonical poset-resolution vertex of the unchanged original finite-projective Q category. -/
def originalQVertex :=
  universalResolutionVertex (FiniteProjectiveModule.exactStructure.{u, u} R).QCategory
    (FiniteProjectiveModule.exactStructure.{u, u} R).qZero

/-- The literal compact-open metric-order based loop carrier. -/
abbrev OriginalQMetricLoops := Path (vertex (originalQVertex R)) (vertex (originalQVertex R))

/-- Genuine homotopy equivalence from these actual metric loops to the original Q loop target. -/
def originalQMetricLoopEquiv :
    ContinuousMap.HomotopyEquiv (OriginalQMetricLoops R)
      (Path (classifyingSpacePoint (FiniteProjectiveModule.exactStructure.{u, u} R).qZero)
        (classifyingSpacePoint (FiniteProjectiveModule.exactStructure.{u, u} R).qZero)) :=
  (basedRealizationHomotopyEquiv (originalQVertex R)).loopHomotopyEquiv.symm.trans
    (universalResolutionLoopHomotopyEquiv
      (FiniteProjectiveModule.exactStructure.{u, u} R).QCategory
      (FiniteProjectiveModule.exactStructure.{u, u} R).qZero)

/-- The forward function is cutoff reconstruction followed by the original resolution map. -/
theorem originalQMetricLoopEquiv_apply (γ : OriginalQMetricLoops R) (t : I) :
    originalQMetricLoopEquiv R γ t =
      (universalResolutionBasedHomotopyEquiv
        (FiniteProjectiveModule.exactStructure.{u, u} R).QCategory
        (FiniteProjectiveModule.exactStructure.{u, u} R).qZero).toMap
          (cutoffRealizationMap (γ t)) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- The original constant Q loop is preserved exactly. -/
theorem originalQMetricLoopEquiv_refl :
    originalQMetricLoopEquiv R (Path.refl (vertex (originalQVertex R))) =
      Path.refl (classifyingSpacePoint (FiniteProjectiveModule.exactStructure.{u, u} R).qZero) := by
  change universalResolutionLoopHomotopyEquiv
    (FiniteProjectiveModule.exactStructure.{u, u} R).QCategory
    (FiniteProjectiveModule.exactStructure.{u, u} R).qZero
      (basedLoopMap cutoffRealizationMap (cutoffRealizationMap_vertex (originalQVertex R))
        (Path.refl (vertex (originalQVertex R)))) = _
  rw [basedLoopMap_refl]
  exact universalResolutionLoopHomotopyEquiv_refl
    (FiniteProjectiveModule.exactStructure.{u, u} R).QCategory
    (FiniteProjectiveModule.exactStructure.{u, u} R).qZero

/-- The actual Q-related metric loop model has a genuine local connector. -/
def originalQMetricLoopConnector : LocalEquiconnection (OriginalQMetricLoops R) :=
  loopEquiconnection (originalQVertex R)

/-- Every original path in that model has an actual open connector-convex neighborhood. -/
theorem originalQMetricLoopConvexNeighborhood (γ : OriginalQMetricLoops R) :
    ∃ W : Set (OriginalQMetricLoops R),
      IsOpen W ∧ γ ∈ W ∧ (originalQMetricLoopConnector R).IsConvex W :=
  exists_convex_open_loop_neighborhood (originalQVertex R) γ

/-- The forward-after-inverse composite in the actual Q target has the supplied homotopy. -/
def originalQLoopInversePath
    (γ : Path (classifyingSpacePoint (FiniteProjectiveModule.exactStructure.{u, u} R).qZero)
      (classifyingSpacePoint (FiniteProjectiveModule.exactStructure.{u, u} R).qZero)) :
    Path (originalQMetricLoopEquiv R ((originalQMetricLoopEquiv R).invFun γ)) γ :=
  (originalQMetricLoopEquiv R).right_inv.some.evalAt γ

end Consumer.MetricOrderLoops
