/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.KTheory.GrothendieckComparison.Basic

/-!
# Normalization of Q-edge loops

Every individual Q-arrow, closed to a based loop using the canonical zero-apex
paths, represents the object class of the kernel of its left span leg. These
are statements about actual arrow paths and do not assume arbitrary continuous
loops are edge paths.
-/
@[expose] public section


noncomputable section
universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.ExactStructure
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C)

/-- Every admissible span factors as the reverse quotient followed by the
forward inclusion. -/
lemma qSpan_factor {X Y : C} (s : Span E.deflation E.inflation X Y) :
    Q.mkHom E.deflation E.inflation s =
      E.qDeflation s.l s.wl ≫ E.qInflation s.r s.wr := by
  symm
  have h : IsPullback (𝟙 s.apex) (𝟙 s.apex) (𝟙 s.apex) (𝟙 s.apex) :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  apply E.q_comp_of_isPullback _ _ _ _ h s (Iso.refl _)
  · simp
  · simp

/-- Close a Q-arrow to a based endomorphism in any groupoid-valued image,
using the canonical zero-apex arrows. -/
def qEdgeClass {D : Type*} [Groupoid D] (F : E.QCategory ⥤ D)
    {X Y : E.QCategory} (f : X ⟶ Y) : End (F.obj E.qZero) :=
  F.map (E.fromZero X) ≫ F.map f ≫ inv (F.map (E.fromZero Y))

/-- An admissible inclusion contributes a trivial closed edge. -/
@[simp] lemma qEdgeClass_qInflation {D : Type*} [Groupoid D] (F : E.QCategory ⥤ D)
    {X Y : C} (i : X ⟶ Y) (hi : E.inflation i) :
    E.qEdgeClass F (E.qInflation i hi) = 1 := by
  dsimp only [qEdgeClass]
  rw [← Category.assoc, ← F.map_comp, E.fromZero_qInflation]
  exact IsIso.hom_inv_id _

/-- Closed-edge classes respect concatenation, with the endomorphism group
multiplication convention made explicit. -/
lemma qEdgeClass_comp {D : Type*} [Groupoid D] (F : E.QCategory ⥤ D)
    {X Y Z : E.QCategory} (f : X ⟶ Y) (g : Y ⟶ Z) :
    E.qEdgeClass F (f ≫ g) = E.qEdgeClass F g * E.qEdgeClass F f := by
  change _ = (_ ≫ _ ≫ _) ≫ (_ ≫ _ ≫ _)
  simp [qEdgeClass, Category.assoc]

/-- Closing the Q-arrow of an admissible quotient yields its kernel object
class. -/
lemma qEdgeClass_qDeflation {D : Type*} [Groupoid D] (F : E.QCategory ⥤ D)
    {S : ShortComplex C} (hS : E.conflation S) :
    E.qEdgeClass F (E.qDeflation S.g (E.deflation_of_conflation hS)) =
      E.qObjectClass F S.X₁ := by
  have h₁ := congrArg F.map (E.fromZero_qInflation S.f (E.inflation_of_conflation hS))
  have h₂ := congrArg F.map (E.conflation_q_relation hS)
  simp only [Functor.map_comp] at h₁ h₂
  dsimp only [qEdgeClass, qObjectClass]
  apply (cancel_mono (F.map (E.fromZero (Q.of E.deflation E.inflation S.X₂)))).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h₁]
  simp only [IsIso.inv_hom_id_assoc]
  exact h₂

/-- Every represented Q-arrow has a closed-edge class equal to an object class. -/
lemma qEdgeClass_span {D : Type*} [Groupoid D] (F : E.QCategory ⥤ D)
    {X Y : C} (s : Span E.deflation E.inflation X Y) :
    ∃ K : C, E.qEdgeClass F (Q.mkHom E.deflation E.inflation s) = E.qObjectClass F K := by
  obtain ⟨K, i, hi, hS⟩ := s.wl
  refine ⟨K, ?_⟩
  rw [E.qSpan_factor, E.qEdgeClass_comp, E.qEdgeClass_qInflation, one_mul]
  exact E.qEdgeClass_qDeflation F hS

/-- The normalization applies to every actual Q-morphism, independently of
its chosen span representative. -/
lemma qEdgeClass_eq_objectClass {D : Type*} [Groupoid D] (F : E.QCategory ⥤ D)
    {X Y : E.QCategory} (f : X ⟶ Y) :
    ∃ K : C, E.qEdgeClass F f = E.qObjectClass F K := by
  rcases X with ⟨⟨X⟩⟩
  rcases Y with ⟨⟨Y⟩⟩
  refine Quotient.inductionOn f (fun s => ?_)
  exact E.qEdgeClass_span F s

/-- The actual K₀ class of a realized Q-edge closed using canonical paths. -/
def kZeroEdgeClass {X Y : E.QCategory} (f : X ⟶ Y) : E.K 0 :=
  E.kZeroFundamentalGroupEquiv.symm
    (E.qEdgeClass (classifyingFundamentalGroupoidFunctor E.QCategory) f)

/-- Every closed realized Q-edge belongs to the canonical-generator subgroup. -/
theorem kZeroEdgeClass_mem_objectSubgroup {X Y : E.QCategory} (f : X ⟶ Y) :
    E.kZeroEdgeClass f ∈ E.kZeroObjectSubgroup := by
  obtain ⟨K, hK⟩ := E.qEdgeClass_eq_objectClass
    (classifyingFundamentalGroupoidFunctor E.QCategory) f
  have h : E.kZeroEdgeClass f = E.kZeroObjectClass K := by
    apply E.kZeroFundamentalGroupEquiv.injective
    simpa [kZeroEdgeClass, E.kZeroObjectLoop_eq_qObjectClass] using hK
  rw [h]
  exact Subgroup.subset_closure ⟨K, rfl⟩

end Quillen.ExactStructure
