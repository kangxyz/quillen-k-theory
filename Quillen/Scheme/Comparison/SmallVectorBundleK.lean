import Quillen.Scheme.KTheory
import Quillen.KTheory.Map.CommonAmbient

/-!
# Public small-model scheme K-theory and the actual vector-bundle Q-model

Both Q-categories live in the same universe `u+1`, although the original
vector-bundle category has homs in `u` and its small model has homs in `u+1`.
The genuine exact small-model equivalence therefore induces an actual
based K-group equivalence. No cross-universe realization assertion is used.
-/
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
  ExactStructure.smallModelToOriginal.{u + 1} (vectorBundleExactStructure X)

/-- Public scheme K-theory maps canonically to the actual vector-bundle Q-model. -/
def smallVectorBundleKMap (X : Scheme.{u}) (n : ℕ) :
    Quillen.Scheme.K X n →* (vectorBundleExactStructure X).K n :=
  (smallVectorBundleToOriginal X).commonAmbientKMap n

/-- The public small presentation and actual vector-bundle Q-model have
canonically equivalent K-groups in the same realization universe. -/
def smallVectorBundleKEquiv (X : Scheme.{u}) (n : ℕ) :
    Quillen.Scheme.K X n ≃* (vectorBundleExactStructure X).K n :=
  (smallVectorBundleToOriginal X).commonAmbientKEquiv n

@[simp] theorem smallVectorBundleKEquiv_toMonoidHom (X : Scheme.{u}) (n : ℕ) :
    (smallVectorBundleKEquiv X n).toMonoidHom = smallVectorBundleKMap X n := rfl

end Quillen.SchemeSheaf
