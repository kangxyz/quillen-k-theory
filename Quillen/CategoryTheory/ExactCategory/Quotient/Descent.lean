/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.ExactCategory.Quotient.Conflations
public import Quillen.CategoryTheory.ExactCategory.Functor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Descent of exact functors annihilating the subcategory

An exact functor vanishing on the exact subcategory inverts the genuine weak
isomorphisms. Hence it descends to the actual categorical quotient. Under
either filtering hypothesis this descent is additive and preserves the
specified quotient conflations. No exact structure on the quotient is assumed.
-/
@[expose] public section


noncomputable section
universe v u v' u'
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Quillen.ExactFunctor
variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
  [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  {E : ExactStructure C} {E' : ExactStructure D}
  (F : ExactFunctor E E') (A : ObjectProperty C)

/-- Vanishing on objects of the chosen full subcategory. -/
def VanishesOn : Prop := ∀ X : C, A X → IsZero (F.toFunctor.obj X)

/-- Exact functors annihilating the subcategory invert all weak isomorphisms,
by the actual kernel/cokernel properties of their images. -/
lemma inverts_weakIsomorphisms (hF : F.VanishesOn A) :
    (E.weakIsomorphisms A).IsInvertedBy F.toFunctor := by
  apply (E.weakIsomorphisms_isInvertedBy_iff A F.toFunctor).2
  constructor
  · rintro X Y i ⟨Z, p, h, hS, hZ⟩
    let S := ShortComplex.mk i p h
    exact KernelFork.IsLimit.isIso_ι _
      (E'.kernel (S.map F.toFunctor) (F.map_conflation S hS))
      ((hF Z hZ).eq_of_tgt _ _)
  · rintro X Y p ⟨Z, i, h, hS, hZ⟩
    let S := ShortComplex.mk i p h
    exact CokernelCofork.IsColimit.isIso_π _
      (E'.cokernel (S.map F.toFunctor) (F.map_conflation S hS))
      ((hF Z hZ).eq_of_src _ _)

/-- Conversely, any exact functor inverting these weak isomorphisms vanishes
on the subcategory. -/
lemma vanishesOn_of_inverts_weakIsomorphisms
    (hF : (E.weakIsomorphisms A).IsInvertedBy F.toFunctor) : F.VanishesOn A := by
  intro X hX
  let := hF (0 : X ⟶ 0)
    (E.deflationWithKernel_le_weakIsomorphisms A _ (E.deflationWithKernel_to_zero A hX))
  exact (asIso (F.toFunctor.map (0 : X ⟶ 0))).isZero_iff.2
    (F.toFunctor.map_isZero (isZero_zero C))

lemma vanishesOn_iff_inverts_weakIsomorphisms :
    F.VanishesOn A ↔ (E.weakIsomorphisms A).IsInvertedBy F.toFunctor :=
  ⟨F.inverts_weakIsomorphisms A, F.vanishesOn_of_inverts_weakIsomorphisms A⟩

/-- The actual functor descended along the categorical localization. -/
def quotientDesc (hF : F.VanishesOn A) : ExactQuotient E A ⥤ D :=
  ExactQuotient.lift E A F.toFunctor (F.inverts_weakIsomorphisms A hF)

@[simp]
lemma Q_comp_quotientDesc (hF : F.VanishesOn A) :
    ExactQuotient.Q E A ⋙ F.quotientDesc A hF = F.toFunctor :=
  ExactQuotient.Q_comp_lift E A F.toFunctor (F.inverts_weakIsomorphisms A hF)


variable [Preadditive (ExactQuotient E A)] [(ExactQuotient.Q E A).Additive]

/-- The descended functor is additive under left filtering. -/
lemma quotientDesc_additive_left (hA : E.LeftFiltering A) (hF : F.VanishesOn A) :
    (F.quotientDesc A hF).Additive := by
  let := hA.hasLeftCalculusOfFractions E A
  apply (Localization.functor_additive_iff (ExactQuotient.Q E A)
    (E.weakIsomorphisms A) (F.quotientDesc A hF)).2
  rw [F.Q_comp_quotientDesc A hF]
  infer_instance

/-- The same additivity assertion follows from right fractions by duality. -/
lemma quotientDesc_additive_right (hA : E.RightFiltering A) (hF : F.VanishesOn A) :
    (F.quotientDesc A hF).Additive := by
  let := hA.hasRightCalculusOfFractions E A
  let hc : (ExactQuotient.Q E A ⋙ F.quotientDesc A hF).Additive := by
    rw [F.Q_comp_quotientDesc A hF]
    infer_instance
  let : (F.quotientDesc A hF).op.Additive :=
    (Localization.functor_additive_iff (ExactQuotient.Q E A).op
      (E.weakIsomorphisms A).op (F.quotientDesc A hF).op).2
      (Functor.op_additive (ExactQuotient.Q E A ⋙ F.quotientDesc A hF))
  exact Functor.unop_additive (F.quotientDesc A hF).op

/-- Descent preserves the specified quotient conflations. This is the exact
functor universal property at the level of the actual conflation class. -/
lemma quotientDesc_map_conflation (hF : F.VanishesOn A)
    [(F.quotientDesc A hF).Additive]
    {T : ShortComplex (ExactQuotient E A)} (hT : ExactQuotient.conflation E A T) :
    E'.conflation (T.map (F.quotientDesc A hF)) := by
  obtain ⟨S, hS, ⟨e⟩⟩ := hT
  apply E'.iso_closed (((F.quotientDesc A hF).mapShortComplex).mapIso e)
  change E'.conflation (S.map (ExactQuotient.Q E A ⋙ F.quotientDesc A hF))
  simpa only [F.Q_comp_quotientDesc A hF] using F.map_conflation S hS

end Quillen.ExactFunctor
