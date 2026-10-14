/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassBottomCommonFamily

/-! Actual functor components of the six bottom/chart common boundary nodes.
These equalities do not yet identify the dependent reference-isomorphism components. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes.BassBottomCommonFamily
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

theorem plus_source_functor : (nodes P u v 15).1.functor = (nodes P u v 42).1.functor := rfl
theorem plus_intermediate_functor : (nodes P u v 16).1.functor =
    (nodes P u v 43).1.functor := rfl
theorem plus_target_functor : (nodes P u v 17).1.functor = (nodes P u v 44).1.functor := rfl

theorem minus_source_functor : (nodes P u v 33).1.functor = (nodes P u v 48).1.functor := rfl
theorem minus_intermediate_functor : (nodes P u v 34).1.functor =
    (nodes P u v 49).1.functor := rfl
theorem minus_target_functor : (nodes P u v 35).1.functor = (nodes P u v 50).1.functor := rfl

end Quillen.PerfectComplexes.BassBottomCommonFamily
