/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalEquiconnection.OpenComponents
public import Quillen.Topology.MetricOrderComplex.LoopEquiconnection
public import Quillen.Topology.MetricOrderComplex.RealizationHomotopyEquiv
public import Quillen.Topology.ClassifyingSpace.PosetLoop
public import Quillen.Topology.HomotopyEquiv.ComponentSigma

/-!
# Open components of the original categorical based loop space

The genuine poset-resolution and metric-order based loop equivalences give
actual domination by a loop space with a proved local connector. Pulling back
its path components proves openness in the original compact-open Path topology.
Object and morphism universes remain independent throughout.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology
universe u v
namespace Quillen.RankedChainOrder

variable (C : Type u) [Category.{v} C] (c : C)

/-- The literal metric-order loop space of the original category's canonical resolution vertex. -/
abbrev UniversalMetricLoops :=
  Path (MetricOrderComplex.vertex (universalResolutionVertex C c))
    (MetricOrderComplex.vertex (universalResolutionVertex C c))

/-- The actual metric-order and original categorical loop spaces are homotopy equivalent. -/
def universalMetricLoopHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (UniversalMetricLoops C c)
      (Path (classifyingSpacePoint c) (classifyingSpacePoint c)) :=
  (MetricOrderComplex.basedRealizationHomotopyEquiv
    (universalResolutionVertex C c)).loopHomotopyEquiv.symm.trans
      (universalResolutionLoopHomotopyEquiv C c)

/-- Every original categorical based-loop path component is open. -/
theorem isOpen_loop_pathComponent
    (γ : Path (classifyingSpacePoint c) (classifyingSpacePoint c)) :
    IsOpen (pathComponent γ) := by
  let e := universalMetricLoopHomotopyEquiv C c
  exact isOpen_pathComponent_of_domination e.invFun e.toFun e.right_inv.some
    (MetricOrderComplex.loopEquiconnection (universalResolutionVertex C c)).isOpen_pathComponent γ

end Quillen.RankedChainOrder
