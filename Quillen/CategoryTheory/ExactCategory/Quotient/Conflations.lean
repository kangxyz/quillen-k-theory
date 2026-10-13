/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.CategoryTheory.ExactCategory.Quotient.Kernels
public import Quillen.CategoryTheory.ExactCategory.Quotient.Cokernels

/-!
# The specified conflations of the exact quotient

Schlichting's quotient class consists of the sequences isomorphic to images
of ambient conflations. Here this class is defined and its actual kernel and
cokernel universal properties are proved under the respective filtering
hypotheses. The remaining exact axioms and the other universal property for
one-sided s-filtering are not assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits

namespace Quillen.ExactQuotient
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (A : ObjectProperty C)
  [Preadditive (ExactQuotient E A)] [(Q E A).Additive]

/-- The isomorphism-closed class specified in Schlichting, Definition 1.15. -/
def conflation (T : ShortComplex (ExactQuotient E A)) : Prop :=
  ∃ S : ShortComplex C, E.conflation S ∧ Nonempty (S.map (Q E A) ≅ T)

lemma map_conflation {S : ShortComplex C} (hS : E.conflation S) :
    conflation E A (S.map (Q E A)) := ⟨S, hS, ⟨Iso.refl _⟩⟩

lemma conflation_iso_closed {S T : ShortComplex (ExactQuotient E A)} (e : S ≅ T)
    (hS : conflation E A S) : conflation E A T := by
  obtain ⟨U, hU, ⟨f⟩⟩ := hS
  exact ⟨U, hU, ⟨f ≪≫ e⟩⟩

/-- Right filtering proves the genuine kernel property for every specified
quotient conflation, including those presented only up to isomorphism. -/
def quotientConflationKernelIsLimit (hA : E.RightFiltering A)
    {T : ShortComplex (ExactQuotient E A)} (hT : conflation E A T) :
    IsLimit (KernelFork.ofι T.f T.zero) := by
  let S := hT.choose
  have hS := hT.choose_spec.1
  let e := hT.choose_spec.2.some
  exact IsKernel.ofIso _ (conflationKernelIsLimit E A hA hS) _
    (ShortComplex.π₂.mapIso e) (ShortComplex.π₃.mapIso e) (ShortComplex.π₁.mapIso e)
    e.hom.comm₂₃ e.hom.comm₁₂

/-- Left filtering proves the genuine cokernel property for every specified
quotient conflation. -/
def quotientConflationCokernelIsColimit (hA : E.LeftFiltering A)
    {T : ShortComplex (ExactQuotient E A)} (hT : conflation E A T) :
    IsColimit (CokernelCofork.ofπ T.g T.zero) := by
  let S := hT.choose
  have hS := hT.choose_spec.1
  let e := hT.choose_spec.2.some
  exact IsCokernel.ofIso _ (mappedConflationCokernelIsColimit E A hA hS) _
    (ShortComplex.π₁.mapIso e) (ShortComplex.π₂.mapIso e) (ShortComplex.π₃.mapIso e)
    e.hom.comm₁₂ e.hom.comm₂₃

end Quillen.ExactQuotient
