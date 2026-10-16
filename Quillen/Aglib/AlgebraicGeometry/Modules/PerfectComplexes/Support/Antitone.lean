/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Restriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.Complex.DerivedZero
public import Aglib.AlgebraicGeometry.Modules.Complex.Restriction

/-!
# Shrinking the acyclicity open

The original support predicate is antitone in its open of actual acyclicity.
-/
@[expose] public section



open AlgebraicGeometry.Scheme.Modules.Complex



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
universe u
attribute [local instance] Scheme.Modules.standardHasDerivedCategory
namespace Quillen.PerfectComplexes
attribute [local instance] HasDerivedCategory.standard

/-- Shrinking the acyclicity open weakens the original support predicate. -/
lemma perfectSupported_antitone {X : Scheme.{u}} {S T : X.Opens} (h : S ≤ T) :
    perfectSupported T.ι ≤ perfectSupported S.ι := by
  intro K hK
  refine ⟨hK.1, ?_⟩
  rw [← isZero_toDerived_iff_acyclic]
  let c : restrict T.ι ⋙ restrict (X.homOfLE h) ≅ restrict S.ι :=
    restrictCompIso _ _ ≪≫ eqToIso (restrict_congr (Scheme.homOfLE_ι X h))
  exact (isZero_toDerived_restrict_of_isZero (X.homOfLE h)
    ((isZero_toDerived_iff_acyclic _).mpr hK.2)).of_iso
      ((DerivedCategory.Q (C := S.toScheme.Modules)).mapIso (c.app K)).symm

end Quillen.PerfectComplexes

end


end
