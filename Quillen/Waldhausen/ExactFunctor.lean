import Quillen.CategoryTheory.ExactCategory.FunctorPushout
import Quillen.Waldhausen.ExactCategory
import Quillen.Waldhausen.Functor

/-! # Exact Quillen functors are exact Waldhausen functors

The pushout axiom is proved by preservation of the actual biproduct conflation,
not supplied as an extra hypothesis. All other structural conditions follow
from genuine additive exactness and functorial preservation of isomorphisms.
-/

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe v u v' u'

namespace Quillen.ExactFunctor
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasFiniteBiproducts D]
  {EC : ExactStructure C} {ED : ExactStructure D} (F : ExactFunctor EC ED)

/-- Genuine exactness implies all Waldhausen-exact structure conditions. -/
theorem waldhausenExact : Waldhausen.IsExact
    (Waldhausen.ofExactCategory EC).cof (Waldhausen.ofExactCategory EC).weq
    (Waldhausen.ofExactCategory ED).cof (Waldhausen.ofExactCategory ED).weq F.toFunctor where
  zero hZ := F.toFunctor.map_isZero hZ
  cofibration f hf := F.map_inflation f hf
  weak f hf := by
    let : IsIso f := hf
    exact F.toFunctor.map_isIso f
  pushout hi h := F.map_isPushout hi h

end Quillen.ExactFunctor
