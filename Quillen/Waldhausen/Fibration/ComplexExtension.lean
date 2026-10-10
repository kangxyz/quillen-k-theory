/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Waldhausen.Fibration.WeakEquivalenceCofiber
public import Quillen.Waldhausen.ComplexSubcategory
public import Quillen.Algebra.Homology.QuasiIsoExtension

/-! # The structural extension axiom for genuine complex weak equivalences

Displayed cofiber squares give actual short exact sequences. Their homology
four-lemma proof supplies the middle quasi-isomorphism, including in inherited
full subcategories. The extension axiom is derived, not assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
namespace Quillen.Waldhausen.Fibration

section Cofiber
variable {C : Type u} [Category.{v} C] [Abelian C]
  {A B Q Z : C} {i : A ⟶ B} {z : A ⟶ Z} {q : B ⟶ Q} {t : Z ⟶ Q}
  (h : IsPushout i z q t) (hZ : IsZero Z)

include h hZ

/-- The composite in an actual zero-corner pushout vanishes. -/
theorem cofiber_comp_zero : i ≫ q = 0 := by
  rw [h.w, hZ.eq_of_tgt z 0, zero_comp]

/-- The displayed cofiber is the actual categorical cokernel. -/
def cofiberIsCokernel : IsColimit (CokernelCofork.ofπ q (cofiber_comp_zero h hZ)) := by
  refine CokernelCofork.IsColimit.ofπ q (cofiber_comp_zero h hZ)
    (fun a ha ↦ h.desc a (hZ.to_ _) (by rw [hZ.eq_of_tgt z 0, zero_comp]; exact ha)) ?_ ?_
  · intro W a ha
    exact h.inl_desc _ _ _
  · intro W a ha m hm
    apply h.hom_ext
    · rw [h.inl_desc]
      exact hm
    · exact hZ.eq_of_src _ _

/-- A monic cofibration and displayed zero-corner pushout give a short exact sequence. -/
theorem cofiber_shortExact [Mono i] :
    (ShortComplex.mk i q (cofiber_comp_zero h hZ)).ShortExact where
  mono_f := inferInstance
  epi_g := Cofork.IsColimit.epi (cofiberIsCokernel h hZ)
  exact := (ShortComplex.mk i q (cofiber_comp_zero h hZ)).exact_of_g_is_cokernel
    (cofiberIsCokernel h hZ)
end Cofiber

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Actual quasi-isomorphisms on complexes satisfy the structural extension axiom. -/
theorem complexes_extensionAxiom : ExtensionAxiom (complexes A) where
  extension {K L Q K' L' Q'} {i q i' q'} hi hi' h h' a b c wi wq ha hc := by
    let : Mono i := hi
    let : Mono i' := hi'
    let φ : ShortComplex.mk _ _ (cofiber_comp_zero h (complexes A).isZero) ⟶
        ShortComplex.mk _ _ (cofiber_comp_zero h' (complexes A).isZero) :=
      { τ₁ := a, τ₂ := b, τ₃ := c, comm₁₂ := wi.symm, comm₂₃ := wq.symm }
    exact quasiIso_middle_of_shortExact φ (cofiber_shortExact h (complexes A).isZero)
      (cofiber_shortExact h' (complexes A).isZero) ha hc

attribute [local instance] Abelian.hasFiniteBiproducts
variable (P : ObjectProperty (CochainComplex A ℤ))
  [P.ContainsZero] [P.IsClosedUnderIsomorphisms]
  [(abelianExactStructure (CochainComplex A ℤ)).IsExtensionClosed P]
  [P.IsClosedUnderFiniteProducts]

/-- Genuine inherited quasi-isomorphisms satisfy extension in every actual
extension-closed full complex subcategory. No cone/kernel/shift closure is needed. -/
theorem complexSubcategory_extensionAxiom : ExtensionAxiom (complexSubcategory P) where
  extension {K L Q K' L' Q'} {i q i' q'} hi hi' h h' a b c wi wq ha hc := by
    have hiA := (ExactSubcategory.exactInclusion
      (abelianExactStructure (CochainComplex A ℤ)) P).map_inflation _ hi
    have hiA' := (ExactSubcategory.exactInclusion
      (abelianExactStructure (CochainComplex A ℤ)) P).map_inflation _ hi'
    let : Mono i.hom := (abelianExactStructure_inflation_iff _ _).1 hiA
    let : Mono i'.hom := (abelianExactStructure_inflation_iff _ _).1 hiA'
    let hZ := P.ι.map_isZero (complexSubcategory P).isZero
    let H := fullSubcategory_map_pushout _ P hi h
    let H' := fullSubcategory_map_pushout _ P hi' h'
    let φ : ShortComplex.mk _ _ (cofiber_comp_zero H hZ) ⟶
        ShortComplex.mk _ _ (cofiber_comp_zero H' hZ) :=
      { τ₁ := a.hom, τ₂ := b.hom, τ₃ := c.hom,
        comm₁₂ := (congrArg (fun f ↦ f.hom) wi).symm,
        comm₂₃ := (congrArg (fun f ↦ f.hom) wq).symm }
    exact quasiIso_middle_of_shortExact φ (cofiber_shortExact H hZ)
      (cofiber_shortExact H' hZ) ha hc

end Quillen.Waldhausen.Fibration
