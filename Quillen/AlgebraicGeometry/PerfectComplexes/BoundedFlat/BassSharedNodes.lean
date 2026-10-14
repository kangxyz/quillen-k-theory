/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientReferenceSteps

/-! Full dependent node equations for the original chart/bottom common boundary. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassReferenceMerge
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The complete plus source node: actual functor and anchored reference. -/
theorem plus_source_node : BassBottomCommonFamily.nodes P u v 15 =
    BassBottomCommonFamily.nodes P u v 42 := by
  apply Sigma.ext (Model.Hom.ext (BassBottomCommonFamily.plus_source_functor P u v))
  exact heq_of_eq (plus_source_reference P u v)

/-- The complete plus intermediate node: actual functor and anchored reference. -/
theorem plus_intermediate_node : BassBottomCommonFamily.nodes P u v 16 =
    BassBottomCommonFamily.nodes P u v 43 := by
  apply Sigma.ext (Model.Hom.ext (BassBottomCommonFamily.plus_intermediate_functor P u v))
  exact heq_of_eq (plus_intermediate_reference P u v)

/-- The complete plus target node: actual functor and anchored reference. -/
theorem plus_target_node : BassBottomCommonFamily.nodes P u v 17 =
    BassBottomCommonFamily.nodes P u v 44 := by
  apply Sigma.ext (Model.Hom.ext (BassBottomCommonFamily.plus_target_functor P u v))
  exact heq_of_eq (plus_target_reference P u v)

/-- The complete minus source node: actual functor and anchored reference. -/
theorem minus_source_node : BassBottomCommonFamily.nodes P u v 33 =
    BassBottomCommonFamily.nodes P u v 48 := by
  apply Sigma.ext (Model.Hom.ext (BassBottomCommonFamily.minus_source_functor P u v))
  exact heq_of_eq (minus_source_reference P u v)

/-- The complete minus intermediate node: actual functor and anchored reference. -/
theorem minus_intermediate_node : BassBottomCommonFamily.nodes P u v 34 =
    BassBottomCommonFamily.nodes P u v 49 := by
  apply Sigma.ext (Model.Hom.ext (BassBottomCommonFamily.minus_intermediate_functor P u v))
  exact heq_of_eq (minus_intermediate_reference P u v)

/-- The complete minus target node: actual functor and anchored reference. -/
theorem minus_target_node : BassBottomCommonFamily.nodes P u v 35 =
    BassBottomCommonFamily.nodes P u v 50 := by
  apply Sigma.ext (Model.Hom.ext (BassBottomCommonFamily.minus_target_functor P u v))
  exact heq_of_eq (minus_target_reference P u v)

end Quillen.PerfectComplexes.BassReferenceMerge
