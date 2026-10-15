/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.CategoryTheory.TheoremB.StructuredTransitionCalculus
public import Quillen.CategoryTheory.QConstruction.Abelian.SpanFactorization
public import Quillen.Localization.Serre.AuxiliaryLift

/-! # Reduction of all Serre quotient transitions to mapped monos and epis

The proof uses actual quotient-arrow lifts and the genuine epi–mono span
factorization. It does not assume ordinary fixed-source fraction lifting.
-/
@[expose] public section

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- Mapped ambient mono and epi transitions suffice for every mapped Q-span. -/
theorem structuredTransitionIsHE_mapQ_of_mono_epi
    (hm : ∀ {X Y : C} (i : X ⟶ Y) [Mono i],
      TheoremB.StructuredTransitionIsHE (quotientMapQ P)
        ((quotientMapQ P).map (Q.inflationArrow i)))
    (hp : ∀ {X Y : C} (p : Y ⟶ X) [Epi p],
      TheoremB.StructuredTransitionIsHE (quotientMapQ P)
        ((quotientMapQ P).map (Q.surjectionArrow p)))
    {X Y : (abelianExactStructure C).QCategory} (f : X ⟶ Y) :
    TheoremB.StructuredTransitionIsHE (quotientMapQ P) ((quotientMapQ P).map f) := by
  obtain ⟨s, rfl⟩ := Quotient.exists_rep f
  change Q.AbelianSpan X.obj.of Y.obj.of at s
  change TheoremB.StructuredTransitionIsHE (quotientMapQ P) ((quotientMapQ P).map (Q.mkHom _ _ s))
  rw [← Q.span_factorization, Functor.map_comp]
  exact TheoremB.StructuredTransitionIsHE.comp _ (hp s.l) (hm s.r)

/-- Actual fixed-target quotient-arrow lifting reduces all quotient
transitions to mapped ambient monos and epis, plus categorical isomorphisms. -/
theorem structuredTransitions_of_mapped_mono_epi
    (hm : ∀ {X Y : C} (i : X ⟶ Y) [Mono i],
      TheoremB.StructuredTransitionIsHE (quotientMapQ P)
        ((quotientMapQ P).map (Q.inflationArrow i)))
    (hp : ∀ {X Y : C} (p : Y ⟶ X) [Epi p],
      TheoremB.StructuredTransitionIsHE (quotientMapQ P)
        ((quotientMapQ P).map (Q.surjectionArrow p))) :
    TheoremB.StructuredTransitionHomotopyEquivalences (quotientMapQ P) := by
  apply TheoremB.structuredTransitions_of_pointwise
  intro d e f
  let L := P.isoModSerre.Q
  let := Localization.essSurj L P.isoModSerre
  let M := L.objPreimage e.obj.of
  let β : (quotientMapQ P).obj (Q.of (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation M) ≅ e :=
    (quotientExactStructure P).qIsoOfIso (L.objObjPreimageIso e.obj.of)
  obtain ⟨X, g, a, h⟩ := exists_qHom_lift L P (M := M) (V := d.obj.of) (f ≫ β.inv)
  let α : (quotientMapQ P).obj (Q.of (abelianExactStructure C).deflation
      (abelianExactStructure C).inflation X) ≅ d := (quotientExactStructure P).qIsoOfIso a
  have hg : (quotientMapQ P).map g = α.hom ≫ (f ≫ β.inv) := h
  have hf : f = α.inv ≫ (quotientMapQ P).map g ≫ β.hom := by rw [hg]; simp
  rw [hf]
  exact TheoremB.StructuredTransitionIsHE.comp _
    (TheoremB.structuredTransitionIsHE_of_isIso _ α.inv)
    (TheoremB.StructuredTransitionIsHE.comp _
      (structuredTransitionIsHE_mapQ_of_mono_epi P hm hp g)
      (TheoremB.structuredTransitionIsHE_of_isIso _ β.hom))

end Quillen.SerreLocalization
