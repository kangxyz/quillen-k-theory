/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.QConstruction.Connected

/-! # Endomorphisms of the distinguished zero vertex

The distinguished Q-object has only its identity endomorphism. This is much
weaker than being initial, terminal, or a zero object in Q, none of which is
asserted here. The proof uses that a span apex admitting a monomorphism to the
original zero object must itself be zero.
-/
@[expose] public section


noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Quillen.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : Quillen.ExactStructure C)

/-- Every endomorphism of the distinguished zero Q-vertex is the identity. -/
theorem qZero_endomorphism_eq_id (f : E.qZero ⟶ E.qZero) : f = 𝟙 E.qZero := by
  refine Quotient.inductionOn f (fun s => ?_)
  have : Mono s.r := E.mono_of_inflation s.wr
  have hz : IsZero s.apex := (IsZero.iff_id_eq_zero _).2 (by
    apply (cancel_mono s.r).1
    exact (isZero_zero C).eq_of_tgt _ _)
  exact Quillen.Q.mkHom_eq_of_apexIso E.deflation E.inflation s (Span.id (0 : C))
    (hz.iso (isZero_zero C)) ((isZero_zero C).eq_of_tgt _ _) ((isZero_zero C).eq_of_tgt _ _)

instance qZero_endomorphisms_subsingleton : Subsingleton (E.qZero ⟶ E.qZero) where
  allEq f g := (E.qZero_endomorphism_eq_id f).trans (E.qZero_endomorphism_eq_id g).symm

/-- In particular, a comparison isomorphism at the zero vertex is unique. -/
instance qZero_automorphisms_subsingleton : Subsingleton (E.qZero ≅ E.qZero) where
  allEq _ _ := Iso.ext (Subsingleton.elim _ _)

/-- Every Q-hom set with an original zero object as target is a subsingleton.
Existence is not asserted for arbitrary source objects. -/
theorem qHom_subsingleton_of_isZero (X Y : E.QCategory) (hY : IsZero Y.obj.of) :
    Subsingleton (X ⟶ Y) where
  allEq f g := by
    refine Quotient.inductionOn₂ f g (fun s t => ?_)
    have hs : Mono s.r := E.mono_of_inflation s.wr
    have ht : Mono t.r := E.mono_of_inflation t.wr
    have hS : IsZero s.apex := (IsZero.iff_id_eq_zero _).2 (by
      apply (cancel_mono s.r).1
      exact hY.eq_of_tgt _ _)
    have hT : IsZero t.apex := (IsZero.iff_id_eq_zero _).2 (by
      apply (cancel_mono t.r).1
      exact hY.eq_of_tgt _ _)
    exact Quillen.Q.mkHom_eq_of_apexIso E.deflation E.inflation s t
      (hS.iso hT) (hS.eq_of_src _ _) (hS.eq_of_src _ _)

end Quillen.ExactStructure
