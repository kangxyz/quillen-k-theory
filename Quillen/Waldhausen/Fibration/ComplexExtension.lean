/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.CategoryTheory.Abelian.ZeroCornerPushout
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Waldhausen.Fibration.WeakEquivalenceCofiber
public import Quillen.Waldhausen.ComplexSubcategory
public import Quillen.Aglib.Algebra.Homology.CochainComplex.QuasiIsoExtension

/-! # The structural extension axiom for genuine complex weak equivalences

Displayed cofiber squares give actual short exact sequences. Their homology
four-lemma proof supplies the middle quasi-isomorphism, including in inherited
full subcategories. The extension axiom is derived, not assumed.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u v
namespace Quillen.Waldhausen.Fibration

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
