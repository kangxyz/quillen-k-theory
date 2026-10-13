/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.GroupCompletion.ConnectedComponents
public import Quillen.KTheory.Plus.ProjectiveCompletionGradeNaturality
public import Quillen.KTheory.GrothendieckComparison.Equivalence

/-!
# Components of projective completion and the original Quillen K₀

The original numerator-minus-denominator grading identifies categorical
components of projective group completion with the existing exact-category
Grothendieck group. Its inverse is the universal conflation-additive lift of the
actual unit entrance; additivity uses the splitting of projective conflations.
Composing with the existing classical-to-homotopical comparison identifies these
components with the unchanged Quillen K₀. Both comparisons preserve every
original vertex class and commute with right-module change of rings.

No invariant-basis-number, commutativity, cancellation, or stable-freeness
hypothesis is used. This module concerns categorical components and does not
assert a product decomposition of the completion space.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace Quillen.FiniteProjectiveModule

attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
  categoryDirectSumMonoidal categoryDirectSumSymmetric directSumMonoidal directSumSymmetric

variable (R : Type u) [Ring R]

/-- The categorical components of the original projective completion. -/
abbrev CompletionComponents := CategoryTheory.ConnectedComponents (GroupCompletionCategory R)

/-- The original direct sum and coordinate switch give the component group. -/
instance completionComponentsAddCommGroup : AddCommGroup (CompletionComponents R) :=
  inferInstanceAs (AddCommGroup (GroupCompletion.Localization.Components (IsoCategory R)))

/-- The unchanged virtual grading descends to an additive map on components. -/
def completionComponentGrade : CompletionComponents R →+ (exactStructure R).GrothendieckGroup where
  toFun := CategoryTheory.ConnectedComponents.liftFunctor _ (completionGrading R)
  map_zero' := by
    change coreClass R (𝟙_ (IsoCategory R)) - coreClass R (𝟙_ (IsoCategory R)) = 0
    exact sub_self _
  map_add' a b := by
    induction a using Quotient.inductionOn with
    | h X =>
      induction b using Quotient.inductionOn with
      | h Y =>
        change coreClass R (X.obj.2 ⊗ Y.obj.2) - coreClass R (X.obj.1 ⊗ Y.obj.1) =
          (coreClass R X.obj.2 - coreClass R X.obj.1) +
            (coreClass R Y.obj.2 - coreClass R Y.obj.1)
        rw [coreClass_tensor, coreClass_tensor]
        abel

/-- On each original pair the component map is exactly numerator minus denominator. -/
@[simp] theorem completionComponentGrade_mk (X : GroupCompletionCategory R) :
    completionComponentGrade R (CategoryTheory.ConnectedComponents.mk X) =
      completionGrade R X := rfl

/-- A projective module enters the original component group through its unit-denominator pair. -/
def projectiveCompletionClass (P : Category.{u, u} R) : CompletionComponents R :=
  GroupCompletion.Localization.componentUnitClass (⟨P⟩ : IsoCategory R)

/-- The existing grading recovers the original projective object class. -/
@[simp] theorem completionComponentGrade_projectiveCompletionClass (P : Category.{u, u} R) :
    completionComponentGrade R (projectiveCompletionClass R P) =
      (exactStructure R).grothendieckClass P := by
  exact completionGrade_unit_obj R (⟨P⟩ : IsoCategory R)

/-- Splitting a projective conflation proves additivity of the actual component entrance. -/
theorem projectiveCompletionClass_additive :
    (exactStructure R).IsAdditiveInvariant (projectiveCompletionClass R) := by
  intro S hS
  let e : (⟨S.X₂⟩ : IsoCategory R) ≅
      ((⟨S.X₁⟩ : IsoCategory R) ⊗ (⟨S.X₃⟩ : IsoCategory R)) :=
    Core.isoMk ((splittingOfConflation R S hS).isoBinaryBiproduct ≪≫
      biprod.isoCoprod S.X₁ S.X₃)
  exact (GroupCompletion.Localization.componentUnitClass_iso e).trans
    (GroupCompletion.Localization.componentUnitClass_tensor _ _)

/-- The universal conflation-additive map into the actual completion component group. -/
def grothendieckToCompletionComponents :
    (exactStructure R).GrothendieckGroup →+ CompletionComponents R :=
  (exactStructure R).grothendieckLift (projectiveCompletionClass R)
    (projectiveCompletionClass_additive R)

/-- The inverse map retains every original unit-entry object class. -/
@[simp] theorem grothendieckToCompletionComponents_class (P : Category.{u, u} R) :
    grothendieckToCompletionComponents R ((exactStructure R).grothendieckClass P) =
      projectiveCompletionClass R P :=
  (exactStructure R).grothendieckLift_class _ _ P

/-- The existing grading and the original unit-entry lift are inverse on the Grothendieck group. -/
theorem completionComponentGrade_comp :
    (completionComponentGrade R).comp (grothendieckToCompletionComponents R) =
      AddMonoidHom.id (exactStructure R).GrothendieckGroup := by
  apply (exactStructure R).grothendieck_hom_ext
  intro P
  simp

/-- The numerator-minus-denominator identity proves the other inverse on every component. -/
theorem grothendieckToCompletionComponents_grade (a : CompletionComponents R) :
    grothendieckToCompletionComponents R (completionComponentGrade R a) = a := by
  induction a using Quotient.inductionOn with
  | h X =>
    rw [completionComponentGrade_mk]
    change grothendieckToCompletionComponents R
      ((exactStructure R).grothendieckClass X.obj.2.of -
        (exactStructure R).grothendieckClass X.obj.1.of) = _
    rw [map_sub, grothendieckToCompletionComponents_class,
      grothendieckToCompletionComponents_class]
    exact (GroupCompletion.Localization.componentClass_pair_eq_sub X.obj.1 X.obj.2).symm

/-- The original virtual grading is the additive equivalence on completion components. -/
def completionComponentGrothendieckEquiv :
    CompletionComponents R ≃+ (exactStructure R).GrothendieckGroup where
  toFun := completionComponentGrade R
  invFun := grothendieckToCompletionComponents R
  left_inv := grothendieckToCompletionComponents_grade R
  right_inv := DFunLike.congr_fun (completionComponentGrade_comp R)
  map_add' := (completionComponentGrade R).map_add

/-- The equivalence has exactly the original virtual grading on every original vertex. -/
@[simp] theorem completionComponentGrothendieckEquiv_mk (X : GroupCompletionCategory R) :
    completionComponentGrothendieckEquiv R (CategoryTheory.ConnectedComponents.mk X) =
      completionGrade R X := rfl

/-- Two original vertices admit a finite zigzag exactly when their original virtual grades agree. -/
theorem completion_zigzag_iff_grade_eq (X Y : GroupCompletionCategory R) :
    Zigzag X Y ↔ completionGrade R X = completionGrade R Y := by
  rw [← GroupCompletion.Localization.componentClass_eq_iff]
  exact (completionComponentGrothendieckEquiv R).injective.eq_iff.symm

/-- Categorical components identify with the preexisting homotopical Quillen K₀. -/
def completionComponentKZeroEquiv : CompletionComponents R ≃ (exactStructure R).K 0 :=
  (completionComponentGrothendieckEquiv R).toEquiv.trans
    (Multiplicative.ofAdd.trans (exactStructure R).grothendieckKZeroEquiv.toEquiv)

/-- The K₀ equivalence preserves the original virtual class of every completion vertex. -/
@[simp] theorem completionComponentKZeroEquiv_mk (X : GroupCompletionCategory R) :
    completionComponentKZeroEquiv R (CategoryTheory.ConnectedComponents.mk X) =
      completionKZeroClass R X := rfl

/-- On an original pair the K₀ equivalence is numerator class divided by denominator class. -/
theorem completionComponentKZeroEquiv_pair (A B : IsoCategory R) :
    completionComponentKZeroEquiv R (CategoryTheory.ConnectedComponents.mk (completionPair R A B)) =
      (exactStructure R).kZeroObjectClass B.of / (exactStructure R).kZeroObjectClass A.of :=
  completionKZeroClass_eq_objectClasses R (completionPair R A B)

variable {R} {S : Type u} [Ring S]

/-- The actual change-of-rings functor induces this map on the original component quotients. -/
def completionComponentsBaseChange (f : R →+* S) :
    CompletionComponents Rᵐᵒᵖ → CompletionComponents Sᵐᵒᵖ :=
  (completionBaseChange f).mapConnectedComponents

/-- The quotient map uses the original change-of-rings image of every vertex. -/
@[simp] theorem completionComponentsBaseChange_mk (f : R →+* S)
    (X : GroupCompletionCategory Rᵐᵒᵖ) :
    completionComponentsBaseChange f (CategoryTheory.ConnectedComponents.mk X) =
      CategoryTheory.ConnectedComponents.mk ((completionBaseChange f).obj X) := rfl

/-- The component equivalence commutes with the original right-module change of rings. -/
theorem completionComponentGrothendieckEquiv_baseChange (f : R →+* S)
    (a : CompletionComponents Rᵐᵒᵖ) :
    completionComponentGrothendieckEquiv Sᵐᵒᵖ (completionComponentsBaseChange f a) =
      (rightBaseChangeExact f).grothendieckMap (completionComponentGrothendieckEquiv Rᵐᵒᵖ a) := by
  induction a using Quotient.inductionOn with
  | h X => exact completionGrade_baseChange f X

/-- Naturality reaches the unchanged original homotopical Quillen K₀ map. -/
theorem completionComponentKZeroEquiv_baseChange (f : R →+* S)
    (a : CompletionComponents Rᵐᵒᵖ) :
    (rightBaseChangeExact f).KMap 0 (completionComponentKZeroEquiv Rᵐᵒᵖ a) =
      completionComponentKZeroEquiv Sᵐᵒᵖ (completionComponentsBaseChange f a) := by
  induction a using Quotient.inductionOn with
  | h X => exact completionKZeroClass_baseChange f X

end Quillen.FiniteProjectiveModule
