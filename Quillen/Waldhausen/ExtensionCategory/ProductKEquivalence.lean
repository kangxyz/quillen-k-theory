import Quillen.Waldhausen.ExtensionCategory.KEquivalence
import Quillen.Waldhausen.Product.KEquivalence

/-! # Full canonical extension-category K-additivity

The target is now the ordinary product of the original K-groups. The
forward homomorphism is exactly the source and cofiber canonical K-maps.
-/

noncomputable section
open CategoryTheory
universe u

namespace Quillen.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{u} C] (W : Structure C)

/-- The actual extension-category K-groups are the product of source and cofiber K-groups. -/
def productKEquiv (n : ℕ) : (waldhausenStructure W).K n ≃* W.K n × W.K n :=
  (KEquiv W n).trans (Product.KEquiv W W n)

/-- Full additivity retains the original two canonical homomorphisms. -/
theorem productKEquiv_toMonoidHom (n : ℕ) :
    (productKEquiv W n).toMonoidHom =
      (KMap (source_exact W) n).prod (KMap (cofiber_exact W) n) := by
  apply MonoidHom.ext
  intro q
  apply _root_.Prod.ext
  · change KMap (fst_exact W W) n (KMap (sourceCofiber_exact W) n q) = KMap (source_exact W) n q
    exact (DFunLike.congr_fun (KMap_comp (sourceCofiber_exact W) (fst_exact W W) n) q).symm
  · change KMap (snd_exact W W) n (KMap (sourceCofiber_exact W) n q) = KMap (cofiber_exact W) n q
    exact (DFunLike.congr_fun (KMap_comp (sourceCofiber_exact W) (snd_exact W W) n) q).symm

end Quillen.Waldhausen.ExtensionCategory
