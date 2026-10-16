/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlatPullback

/-!
# Original perfect restriction and flat pullback

The actual geometric restriction comparison retains its specified original left unitor.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen 
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The original restriction/flat-pullback isomorphism, including its actual left unitor. -/
def perfectOpenRestrictionFlatIso :
    (𝟭 (Perfect X)) ⋙ perfectRestrict j ≅ perfectFlatPullback j :=
  Functor.leftUnitor (perfectRestrict j) ≪≫ perfectRestrictIsoFlatPullback j

end Quillen.PerfectComplexes

end

end
