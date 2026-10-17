/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedBelow.Basic
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Strict

/-!
# Strict perfectness gives the original lower-term bound

The displayed strict-perfect term window supplies the unchanged lower-bounded object predicate.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite ModuleCat
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Complex HomologicalComplex CochainComplex
namespace Quillen.PerfectComplexes.ProjectiveLine.Euler
/-- Strict boundedness supplies an actual term lower bound. -/
lemma boundedBelow_of_strictPerfect {X : Scheme.{u}} {K : CochainComplex X.Modules ℤ}
    (hK : strictPerfect X K) : BoundedBelow.objects X K := by
  obtain ⟨a, b, hab⟩ := hK.1
  exact ⟨locallyPerfect_of_strictPerfect hK, a,
    (CochainComplex.isStrictlyGE_iff _ a).mpr (fun i hi => hab i (Or.inl hi))⟩


end Quillen.PerfectComplexes.ProjectiveLine.Euler
end
end
