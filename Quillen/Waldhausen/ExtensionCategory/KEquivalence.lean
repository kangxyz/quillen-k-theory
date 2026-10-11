/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.ExtensionCategory.Realization
public import Quillen.Waldhausen.Functoriality.KEquivalence

/-! # Canonical K-theory additivity for the actual extension category

The forward homomorphism is exactly the original canonical K-map of
(source, cofiber), and the inverse is exactly the original canonical K-map
of the literal split extension. The target is the actual Waldhausen
product-category K-theory; no unproved realization-product comparison is used.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u

namespace Quillen.Waldhausen.ExtensionCategory
variable {C : Type u} [Category.{u} C] (W : Structure C)

/-- Genuine extension-category K-additivity by the original source/cofiber K-map.
The common object/hom universe is retained explicitly. -/
def KEquiv (n : ℕ) : (waldhausenStructure W).K n ≃* (productStructure W W).K n :=
  KEquivOfRealization (sourceCofiber_exact W) (realizationHomotopyEquiv W)
    (realizationHomotopyEquiv_toFun W) n

/-- This is exactly the original canonical source/cofiber homomorphism. -/
@[simp] theorem KEquiv_coe (n : ℕ) :
    (↑(KEquiv W n) : (waldhausenStructure W).K n →* (productStructure W W).K n) = KMap
        (sourceCofiber_exact W) n := rfl


/-- The original canonical split-extension homomorphism, using coproducts
whose existence is supplied by the Waldhausen axioms. -/
def splitKMap (n : ℕ) : (productStructure W W).K n →* (waldhausenStructure W).K n := by
  letI := Additivity.hasBinaryCoproducts W
  letI := Additivity.hasBinaryCoproducts (waldhausenStructure W)
  exact KMap (split_exact W) n

/-- The inverse of extension additivity is exactly the actual canonical split
K-map, proved by the genuine split-cofiber natural isomorphism. -/
theorem KEquiv_symm_toMonoidHom (n : ℕ) :
    (KEquiv W n).symm.toMonoidHom = splitKMap W n := by
  let := Additivity.hasBinaryCoproducts W
  let := Additivity.hasBinaryCoproducts (waldhausenStructure W)
  have h := KMap_eq_of_iso ((split_exact W).comp (sourceCofiber_exact W))
    (IsExact.id (productStructure W W).cof (productStructure W W).weq)
    (splitSourceCofiberIso W) n
  rw [← KMap_comp_KMap (split_exact W) (sourceCofiber_exact W) n, KMap_id] at h
  ext q
  apply (KEquiv W n).injective
  change (KEquiv W n) ((KEquiv W n).symm q) =
    KMap (sourceCofiber_exact W) n (KMap (split_exact W) n q)
  rw [MulEquiv.apply_symm_apply]
  exact (DFunLike.congr_fun h q).symm

end Quillen.Waldhausen.ExtensionCategory
