/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Strict
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Support.Perfect

/-!
# Inclusion from strict supported complexes

The actual full-subcategory inclusion preserves the original underlying complex and chain maps.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry HomologicalComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Literal original supported inclusion underlying the already public K-map. -/
def strictSupportedToPerfect : (strictSupported j).FullSubcategory ⥤
    (perfectSupported j).FullSubcategory :=
  ObjectProperty.ιOfLE (fun _ h => ⟨locallyPerfect_of_strictPerfect h.1, h.2⟩)

end Quillen.PerfectComplexes

end

end
