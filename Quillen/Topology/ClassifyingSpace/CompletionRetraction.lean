/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Topology.ClassifyingSpace.FundamentalGroup
public import Quillen.Topology.ClassifyingSpace.GroupoidCompletion

/-!
# The original groupoid-completion comparison is split injective

Realizing the genuine localization functor and applying the fundamental-group
theorem for groupoids gives a left inverse to the original completed-edge-loop
realization map. No edge-path generation or presentation theorem for arbitrary
topological paths is assumed. Object and morphism universes are independent.
-/
@[expose] public section

noncomputable section
universe u v
open CategoryTheory Opposite
open scoped Simplicial Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen
variable (C : Type u) [Category.{v} C]

/-- The nerve map of the genuine groupoid-localization functor, expressed by
postcomposition so that independent category universes are preserved. -/
def groupoidCompletionNerveMap :
    nerve C ⟶ nerve (⊤ : MorphismProperty C).Localization where
  app _ := ↾fun F ↦ F ⋙ (⊤ : MorphismProperty C).Q
  naturality _ _ _ := by ext F; rfl

/-- Realization of the genuine localization functor. -/
def classifyingSpaceCompletionMap :
    ClassifyingSpace C ⟶ ClassifyingSpace (⊤ : MorphismProperty C).Localization :=
  SSet.toTop.map (groupoidCompletionNerveMap C)

@[simp] theorem classifyingSpaceCompletionMap_point (c : C) :
    classifyingSpaceCompletionMap C (classifyingSpacePoint c) =
      classifyingSpacePoint ((⊤ : MorphismProperty C).Q.obj c) := by
  change SSet.toTop.map (groupoidCompletionNerveMap C) (realizationPoint (nerveVertex c)) = _
  rw [realizationPoint_naturality]
  exact congrArg realizationPoint (ComposableArrows.ext₀ rfl)

/-- The localization nerve map preserves each original realized edge exactly. -/
theorem classifyingSpaceCompletionMap_path {c d : C} (f : c ⟶ d) :
    ((classifyingSpacePath f).map (classifyingSpaceCompletionMap C).hom.continuous).cast
      (classifyingSpaceCompletionMap_point C c).symm
      (classifyingSpaceCompletionMap_point C d).symm =
      classifyingSpacePath ((⊤ : MorphismProperty C).Q.map f) := by
  ext t
  change SSet.toTop.map (groupoidCompletionNerveMap C) (classifyingSpacePath f t) = _
  have he : (groupoidCompletionNerveMap C).app (op ⦋1⦌) (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₁ ((⊤ : MorphismProperty C).Q.map f) :=
    ComposableArrows.ext₁ rfl rfl (by simp [groupoidCompletionNerveMap])
  exact (realizationEdgePath_naturality_apply (groupoidCompletionNerveMap C)
    (CategoryTheory.nerve.edgeMk f) t).trans
      (congrArg (fun e : (nerve (⊤ : MorphismProperty C).Localization) _⦋1⦌ ↦
        SSet.toTop.map (SSet.yonedaEquiv.symm e) (realizationInterval t)) he)

/-- Realized original arrows commute with the map into the completion's
classifying space, with the actual vertex equalities as components. -/
def classifyingFundamentalGroupoidCompletionNaturality :
    classifyingFundamentalGroupoidFunctor C ⋙
        FundamentalGroupoid.map (classifyingSpaceCompletionMap C).hom ≅
      (⊤ : MorphismProperty C).Q ⋙
        classifyingFundamentalGroupoidFunctor (⊤ : MorphismProperty C).Localization :=
  NatIso.ofComponents (fun c ↦ eqToIso (congrArg FundamentalGroupoid.mk
    (classifyingSpaceCompletionMap_point C c))) (by
    intro c d f
    apply (cancel_epi (eqToHom (congrArg FundamentalGroupoid.mk
      (classifyingSpaceCompletionMap_point C c).symm))).1
    simp only [eqToIso, ← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp]
    rw [Category.assoc]
    change eqToHom (congrArg FundamentalGroupoid.mk
        (classifyingSpaceCompletionMap_point C c).symm) ≫
      (⟦(classifyingSpacePath f).map (classifyingSpaceCompletionMap C).hom.continuous⟧ :
        Path.Homotopic.Quotient _ _) ≫
      eqToHom (congrArg FundamentalGroupoid.mk (classifyingSpaceCompletionMap_point C d)) = _
    rw [FundamentalGroupoid.conj_eqToHom
      (classifyingSpaceCompletionMap_point C c).symm
      (classifyingSpaceCompletionMap_point C d).symm]
    exact congrArg Path.Homotopic.Quotient.mk (classifyingSpaceCompletionMap_path C f))

/-- Extend the original-arrow naturality square over the genuine groupoid
completion by its localization universal property. -/
def classifyingGroupoidCompletionNaturality :
    classifyingGroupoidCompletionFunctor C ⋙
        FundamentalGroupoid.map (classifyingSpaceCompletionMap C).hom ≅
      classifyingFundamentalGroupoidFunctor (⊤ : MorphismProperty C).Localization := by
  let A := classifyingGroupoidCompletionFunctor C ⋙
    FundamentalGroupoid.map (classifyingSpaceCompletionMap C).hom
  let B := classifyingFundamentalGroupoidFunctor (⊤ : MorphismProperty C).Localization
  let Q := (⊤ : MorphismProperty C).Q
  apply Localization.liftNatIso Q ⊤ (Q ⋙ A) (Q ⋙ B) A B
  exact (eqToIso (by
    dsimp only [Q, A]
    rw [← Functor.assoc, toClassifyingGroupoidCompletionFunctor])) ≪≫
      classifyingFundamentalGroupoidCompletionNaturality C

/-- A retraction from actual topological loops to the genuine categorical
completion, obtained from its classifying space and canonical naturality. -/
def classifyingGroupoidCompletionRetraction (c : C) :
    FundamentalGroup (ClassifyingSpace C) (classifyingSpacePoint c) →*
      End ((⊤ : MorphismProperty C).Q.obj c) :=
  let q := (⊤ : MorphismProperty C).Q.obj c
  let e := GroupoidClassifying.fundamentalGroupEquiv q
  let α := (classifyingGroupoidCompletionNaturality C).app q
  e.symm.toMonoidHom.comp (α.conj.toMonoidHom.comp
    ((FundamentalGroupoid.map (classifyingSpaceCompletionMap C).hom).mapEnd
      (FundamentalGroupoid.mk (classifyingSpacePoint c))))

/-- The retraction composed with the ORIGINAL completed-edge realization map
is the identity, with no topological presentation hypothesis. -/
@[simp] theorem classifyingGroupoidCompletionRetraction_comp (c : C) :
    (classifyingGroupoidCompletionRetraction C c).comp (classifyingGroupoidCompletionMap C c) =
      MonoidHom.id _ := by
  apply MonoidHom.ext
  intro a
  apply (GroupoidClassifying.fundamentalGroupEquiv ((⊤ : MorphismProperty C).Q.obj c)).injective
  change GroupoidClassifying.fundamentalGroupEquiv _
    ((GroupoidClassifying.fundamentalGroupEquiv _).symm _) = _
  rw [MulEquiv.apply_symm_apply]
  change ((classifyingGroupoidCompletionNaturality C).app _).conj
    ((classifyingGroupoidCompletionFunctor C ⋙
      FundamentalGroupoid.map (classifyingSpaceCompletionMap C).hom).map a) =
    (classifyingFundamentalGroupoidFunctor (⊤ : MorphismProperty C).Localization).map a
  simp only [Iso.conj_apply, Iso.app_inv, Iso.app_hom]
  rw [(classifyingGroupoidCompletionNaturality C).hom.naturality]
  simp

/-- The canonical realization map on completed loops is injective for every
category, in independent object and morphism universes. -/
theorem classifyingGroupoidCompletionMap_injective (c : C) :
    Function.Injective (classifyingGroupoidCompletionMap C c) := by
  intro a b h
  have he := congrArg (classifyingGroupoidCompletionRetraction C c) h
  simpa only [← MonoidHom.comp_apply, classifyingGroupoidCompletionRetraction_comp,
    MonoidHom.id_apply] using he

end Quillen
