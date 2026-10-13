/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.ClassifyingSpace.NerveGraphData

/-! Every actual nerve-graph point has an original localization-object anchor
whose comparisons with all old vertices and all actual cells are original arrows. -/
@[expose] public section

noncomputable section
open CategoryTheory
attribute [local instance] Localization.groupoid
universe u v
namespace QuillenTest

open Quillen
variable (C : Type u) [Category.{v} C]

/-- The original skeletal pushout supplies compatible categorical anchors at
all actual graph points, including both endpoints of each actual edge. -/
theorem actualNerveGraph_anchor (z : NerveGraphData.Stage C) :
    Nonempty (GraphAttachment.Anchor (NerveGraphData.Index C) (NerveGraphData.pushout C)
      (NerveGraphData.inclusion C) (classifyingGroupoidCompletionFunctor C)
      (NerveGraphData.vertex C) (NerveGraphData.vertexIdentification C) z) :=
  GraphAttachment.anchor_nonempty (NerveGraphData.Index C) (NerveGraphData.pushout C)
    (NerveGraphData.inclusion C) (classifyingGroupoidCompletionFunctor C)
    (NerveGraphData.vertex C) (NerveGraphData.vertexIdentification C)
    (NerveGraphData.edge C) (NerveGraphData.edge_spoke C) z

end QuillenTest
