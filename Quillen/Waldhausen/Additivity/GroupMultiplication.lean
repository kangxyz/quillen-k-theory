import Quillen.Waldhausen.Product.Functoriality
import Quillen.Waldhausen.Additivity.SplitSequence

/-! # Coproduct induces the actual K-group multiplication

The genuine coproduct exact functor and the two genuine zero embeddings
supply a homomorphism from the product K-group with both unit restrictions
equal to the identity. Group algebra identifies it with the existing
multiplication and proves commutativity, including degree zero.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Limits
universe u v

namespace Quillen.Waldhausen.Additivity
open ExtensionCategory
variable {C : Type u} [Category.{v} C] (W : Structure C) [HasBinaryCoproducts C]

/-- The actual binary coproduct functor. -/
def coproductFunctor : C × C ⥤ C :=
  sumFunctor (CategoryTheory.Prod.fst C C) (CategoryTheory.Prod.snd C C)

/-- Binary coproduct is genuinely exact for the componentwise product structure. -/
theorem coproductFunctor_isExact :
    IsExact (productStructure W W).cof (productStructure W W).weq W.cof W.weq
      (coproductFunctor (C := C)) :=
  sumFunctor_isExact (productStructure W W) W (fst_exact W W) (snd_exact W W)

/-- The canonical first zero embedding. -/
def firstEmbedding : C ⥤ C × C := (𝟭 C).prod' (zeroFunctor W)

/-- The canonical second zero embedding. -/
def secondEmbedding : C ⥤ C × C := (zeroFunctor W).prod' (𝟭 C)

omit [HasBinaryCoproducts C] in
theorem firstEmbedding_isExact :
    IsExact W.cof W.weq (productStructure W W).cof (productStructure W W).weq (firstEmbedding W) :=
  pair_exact W W W (IsExact.id W.cof W.weq) (zeroFunctor_isExact W W)

omit [HasBinaryCoproducts C] in
theorem secondEmbedding_isExact :
    IsExact W.cof W.weq (productStructure W W).cof (productStructure W W).weq (secondEmbedding W) :=
  pair_exact W W W (zeroFunctor_isExact W W) (IsExact.id W.cof W.weq)

/-- The literal first coproduct inclusion is a natural isomorphism when the
other summand is the chosen zero. -/
def firstEmbeddingCoproductIso : firstEmbedding W ⋙ coproductFunctor (C := C) ≅ 𝟭 C := by
  let η := sumInl (𝟭 C) (zeroFunctor W)
  have hη (X : C) : IsIso (η.app X) := by
    let : IsIso (W.isZero.to_ W.zero) := W.isZero.isIso W.isZero _
    exact (coprod_isPushout W X W.zero).isIso_inl_of_isIso
  letI : IsIso η := NatIso.isIso_of_isIso_app η
  exact (asIso η).symm

/-- The literal second coproduct inclusion is a natural isomorphism when the
other summand is the chosen zero. -/
def secondEmbeddingCoproductIso : secondEmbedding W ⋙ coproductFunctor (C := C) ≅ 𝟭 C := by
  let η := sumInr (zeroFunctor W) (𝟭 C)
  have hη (X : C) : IsIso (η.app X) := by
    let : IsIso (W.isZero.to_ W.zero) := W.isZero.isIso W.isZero _
    exact (coprod_isPushout W W.zero X).isIso_inr_of_isIso
  letI : IsIso η := NatIso.isIso_of_isIso_app η
  exact (asIso η).symm

/-- The actual coproduct K-map transported through the original product
projection equivalence. -/
def coproductKMap (n : ℕ) : W.K n × W.K n →* W.K n :=
  (KMap (coproductFunctor_isExact W) n).comp (Product.KEquiv W W n).symm.toMonoidHom

theorem coproductKMap_one_right (n : ℕ) (a : W.K n) : coproductKMap W n (a, 1) = a := by
  have he := Product.KEquiv_pair_apply W W W (IsExact.id W.cof W.weq)
    (zeroFunctor_isExact W W) n a
  simp only [KMap_id, KMap_zeroFunctor, MonoidHom.id_apply, MonoidHom.one_apply] at he
  have hi : (Product.KEquiv W W n).symm (a, 1) = KMap (firstEmbedding_isExact W) n a := by
    apply (Product.KEquiv W W n).injective
    simpa only [MulEquiv.apply_symm_apply] using he.symm
  change KMap (coproductFunctor_isExact W) n ((Product.KEquiv W W n).symm (a, 1)) = a
  rw [hi]
  have h := KMap_eq_of_iso ((firstEmbedding_isExact W).comp (coproductFunctor_isExact W))
    (IsExact.id W.cof W.weq) (firstEmbeddingCoproductIso W) n
  rw [KMap_comp, KMap_id] at h
  exact DFunLike.congr_fun h a

theorem coproductKMap_one_left (n : ℕ) (a : W.K n) : coproductKMap W n (1, a) = a := by
  have he := Product.KEquiv_pair_apply W W W (zeroFunctor_isExact W W)
    (IsExact.id W.cof W.weq) n a
  simp only [KMap_id, KMap_zeroFunctor, MonoidHom.id_apply, MonoidHom.one_apply] at he
  have hi : (Product.KEquiv W W n).symm (1, a) = KMap (secondEmbedding_isExact W) n a := by
    apply (Product.KEquiv W W n).injective
    simpa only [MulEquiv.apply_symm_apply] using he.symm
  change KMap (coproductFunctor_isExact W) n ((Product.KEquiv W W n).symm (1, a)) = a
  rw [hi]
  have h := KMap_eq_of_iso ((secondEmbedding_isExact W).comp (coproductFunctor_isExact W))
    (IsExact.id W.cof W.weq) (secondEmbeddingCoproductIso W) n
  rw [KMap_comp, KMap_id] at h
  exact DFunLike.congr_fun h a

/-- Coproduct is exactly the pre-existing group multiplication on K-theory. -/
theorem coproductKMap_eq_mul (n : ℕ) (a b : W.K n) : coproductKMap W n (a, b) = a * b := by
  have he : (a, b) = (a, 1) * (1, b) := by simp
  rw [he, map_mul, coproductKMap_one_right, coproductKMap_one_left]

end Quillen.Waldhausen.Additivity
