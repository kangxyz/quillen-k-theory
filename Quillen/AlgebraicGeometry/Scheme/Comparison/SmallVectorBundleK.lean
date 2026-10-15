/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.Scheme.KTheory
public import Quillen.KTheory.Map.CommonAmbient

/-!
# Public small-model scheme K-theory and the actual vector-bundle Q-model

Both Q-categories live in the same universe `u+1`, although the original
vector-bundle category has homs in `u` and its small model has homs in `u+1`.
The genuine exact small-model equivalence therefore induces an actual
based K-group equivalence. No cross-universe realization assertion is used.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen.SchemeSheaf

/-- The actual exact functor from the public small model to vector bundles. -/
abbrev smallVectorBundleToOriginal (X : Scheme.{u}) :
    ExactFunctor (smallVectorBundleExactStructure X) (vectorBundleExactStructure X) :=
  CategoryTheory.ExactCategory.ExactStructure.smallModelToOriginal.{u + 1}
    (vectorBundleExactStructure X)

/-- Public scheme K-theory maps canonically to the actual vector-bundle Q-model. -/
def smallVectorBundleKMap (X : Scheme.{u}) (n : ℕ) :
    Quillen.Scheme.K X n →* (vectorBundleExactStructure X).K n :=
  (smallVectorBundleToOriginal X).commonAmbientKMap n

/-- The public small presentation and actual vector-bundle Q-model have
canonically equivalent K-groups in the same realization universe. -/
def smallVectorBundleKEquiv (X : Scheme.{u}) (n : ℕ) :
    Quillen.Scheme.K X n ≃* (vectorBundleExactStructure X).K n :=
  (smallVectorBundleToOriginal X).commonAmbientKEquiv n

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem smallVectorBundleKEquiv_coe (X : Scheme.{u}) (n : ℕ) :
    ↑(smallVectorBundleKEquiv X n) = smallVectorBundleKMap X n := rfl

end Quillen.SchemeSheaf
