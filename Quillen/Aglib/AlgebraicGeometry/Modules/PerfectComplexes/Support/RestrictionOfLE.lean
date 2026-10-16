/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Restriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Antitone

/-!
# Restriction with a prescribed support inequality

Actual supported restriction is followed by the literal full-subcategory inclusion that weakens only the acyclicity open.
-/
@[expose] public section



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (S : U.Opens) (T : X.Opens) (h : S ≤ j ⁻¹ᵁ T)

/-- Only the actual support predicate is weakened after original restriction. -/
def perfectSupportedRestrictOfLE : (perfectSupported T.ι).FullSubcategory ⥤
    (perfectSupported S.ι).FullSubcategory :=
  perfectSupportedRestrict j T ⋙ ObjectProperty.ιOfLE (perfectSupported_antitone h)

end Quillen.PerfectComplexes


end

end
