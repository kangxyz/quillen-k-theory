/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalRestriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Extension

/-!
# Exact restriction of locally perfect complexes

The original full-category restriction preserves actual inherited short exact sequences.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex


open CategoryTheory.ExactCategory


noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

instance perfectRestrict_additive : (perfectRestrict j).Additive := by
  unfold perfectRestrict
  infer_instance

/-- Exactness of actual restriction for the inherited exact structures. -/
def perfectExactRestrict : CategoryTheory.ExactCategory.ExactFunctor
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex X.Modules ℤ))
      (locallyPerfect X))
    (ExactSubcategory.exactStructure (abelianExactStructure (CochainComplex U.Modules ℤ))
      (locallyPerfect U)) where
  toFunctor := perfectRestrict j
  map_conflation S hS := by
    change ((S.map (locallyPerfect X).ι).map (restrict j)).ShortExact
    exact hS.map_of_exact _

end Quillen.PerfectComplexes

end

end
