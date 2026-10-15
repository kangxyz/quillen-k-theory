/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.Waldhausen.Additivity.GroupFormula
public import Quillen.Waldhausen.Product.KEquivalence
public import Quillen.Waldhausen.QuillenComparison.KCommutativity
public import Quillen.Waldhausen.QuillenComparison.ExactAdditivity
public import Quillen.Waldhausen.ExtensionCategory.ProductKEquivalence

/-! Downstream contracts for original product, group-law and exact-functor maps. -/
@[expose] public section

open Quillen.Waldhausen


open CategoryTheory.ExactCategory


noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen
universe u v
namespace Consumer
section Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D] (V : Structure C) (W : Structure D)
theorem original_K_zero_commutes (a b : W.K 0) : a * b = b * a :=
  Additivity.K_mul_comm W 0 a b
def original_product_K_equivalence (n : ℕ) :
    (ExtensionCategory.productStructure V W).K n ≃* V.K n × W.K n := Product.KEquiv V W n
theorem original_product_forward (n : ℕ) :
    (original_product_K_equivalence V W n).toMonoidHom =
      (Waldhausen.KMap (ExtensionCategory.fst_exact V W) n).prod
        (Waldhausen.KMap (ExtensionCategory.snd_exact V W) n) := rfl
variable [HasBinaryCoproducts D] {F G H : C ⥤ D}
theorem original_literal_additivity (a : F ⟶ G) (b : G ⟶ H)
    (hs : Additivity.IsCofibrationSequence V W a b) (n : ℕ) (x : V.K n) :
    Waldhausen.KMap hs.exactG n x = Waldhausen.KMap hs.exactF n x * Waldhausen.KMap hs.exactH n x :=
  Additivity.KMap_additivity_mul V W a b hs n x
end Waldhausen
section Quillen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  (E : ExactStructure C) (E' : ExactStructure D)
theorem original_Quillen_K_zero_commutes (a b : E.K 0) : a * b = b * a := E.K_mul_comm 0 a b
theorem original_Quillen_group (n : ℕ) : (E.KCommGroup n).toGroup = inferInstanceAs (Group (E.K n))
  := rfl
theorem original_Quillen_additivity (F G H : ExactFunctor E E')
    (a : F.toFunctor ⟶ G.toFunctor) (b : G.toFunctor ⟶ H.toFunctor) (w : a ≫ b = 0)
    (hc : ∀ X, E'.conflation (ShortComplex.mk (a.app X) (b.app X) (NatTrans.congr_app w X)))
    (n : ℕ) (x : E.K n) : G.KMap n x = F.KMap n x * H.KMap n x :=
  CategoryTheory.ExactCategory.ExactFunctor.KMap_conflation_additivity F G H a b w hc n x
end Quillen
section Extension
variable {C : Type u} [Category.{u} C] (W : Structure C)
def original_full_extension_K_equivalence (n : ℕ) :
    (ExtensionCategory.waldhausenStructure W).K n ≃* W.K n × W.K n :=
  ExtensionCategory.productKEquiv W n
theorem original_full_extension_forward (n : ℕ) :
    (original_full_extension_K_equivalence W n).toMonoidHom =
      (Waldhausen.KMap (ExtensionCategory.source_exact W) n).prod
        (Waldhausen.KMap (ExtensionCategory.cofiber_exact W) n) :=
  ExtensionCategory.productKEquiv_toMonoidHom W n
end Extension
end Consumer
