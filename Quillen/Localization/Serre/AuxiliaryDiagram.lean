/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Localization.Serre.AuxiliaryBaseChange
public import Quillen.Localization.Serre.AuxiliaryLift
public import Quillen.Localization.Serre.AuxiliaryIsoComma
public import Quillen.Localization.Serre.AuxiliaryPostcompose
public import Aglib.CategoryTheory.Abelian.SerreClass.Exact

/-! # The strict diagram of auxiliary categories over ordinary quotient lifts -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace Quillen

/-- Compatible functors are determined by their underlying ordinary functor. -/
theorem QCompatibleFunctor.ext_toFunctor
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    {W V : MorphismProperty C} {W' V' : MorphismProperty D}
    {F G : QCompatibleFunctor W V W' V'} (h : F.toFunctor = G.toFunctor) : F = G := by
  cases F
  cases G
  cases h
  rfl

/-- Equality after forgetting a full-subcategory predicate is equality of functors. -/
theorem fullSubcategoryFunctor_ext
    {C D : Type u} [Category.{u} C] [Category.{u} D] {P : ObjectProperty D}
    {F G : C ⥤ P.FullSubcategory} (h : F ⋙ P.ι = G ⋙ P.ι) : F = G := by
  refine CategoryTheory.Functor.ext (fun X => ObjectProperty.FullSubcategory.ext (Functor.congr_obj
    h X)) ?_
  intro X Y f
  apply ObjectProperty.hom_ext
  simpa only [Functor.comp_map, ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.eqToHom_hom] using Functor.congr_hom h f

namespace SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] Quillen.SerreLocalization.canonicalQuotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]

@[simp]
lemma overPostcomposeQ_id (N : C) : overPostcomposeQ (𝟙 N) = 𝟭 (OverQ N) := by
  have h : overPostcomposeCompatible (𝟙 N) =
      QCompatibleFunctor.id (overDeflation N) (overInflation N) :=
    QCompatibleFunctor.ext_toFunctor (Over.mapId_eq N)
  change (overPostcomposeCompatible (𝟙 N)).mapQ = _
  rw [h]
  exact QCompatibleFunctor.mapQ_id

@[simp]
lemma overPostcomposeQ_comp {M N R : C} (f : M ⟶ N) (g : N ⟶ R) :
    overPostcomposeQ (f ≫ g) = overPostcomposeQ f ⋙ overPostcomposeQ g := by
  have h : overPostcomposeCompatible (f ≫ g) =
      (overPostcomposeCompatible f).comp (overPostcomposeCompatible g) :=
    QCompatibleFunctor.ext_toFunctor (Over.mapComp_eq f g)
  change (overPostcomposeCompatible (f ≫ g)).mapQ = _
  rw [h, QCompatibleFunctor.mapQ_comp]
  rfl

variable (P : ObjectProperty C) [P.IsSerreClass]

@[simp]
lemma auxiliaryPostcompose_id (N : C) :
    auxiliaryPostcompose P (𝟙 N) (P.isoModSerre.id_mem N) = 𝟭 (AuxiliaryKernel P N) := by
  apply fullSubcategoryFunctor_ext
  change (auxiliaryKernelProperty P N).ι ⋙ overPostcomposeQ (𝟙 N) =
    𝟭 (AuxiliaryKernel P N) ⋙ (auxiliaryKernelProperty P N).ι
  rw [overPostcomposeQ_id]
  rfl

@[simp]
lemma auxiliaryPostcompose_comp {M N R : C} (f : M ⟶ N) (g : N ⟶ R)
    (hf : P.isoModSerre f) (hg : P.isoModSerre g) :
    auxiliaryPostcompose P (f ≫ g) (P.isoModSerre.comp_mem f g hf hg) =
      auxiliaryPostcompose P f hf ⋙ auxiliaryPostcompose P g hg := by
  apply fullSubcategoryFunctor_ext
  change (auxiliaryKernelProperty P M).ι ⋙ overPostcomposeQ (f ≫ g) =
    ((auxiliaryKernelProperty P M).ι ⋙ overPostcomposeQ f) ⋙ overPostcomposeQ g
  rw [overPostcomposeQ_comp]
  rfl

/-- The actual strict Cat-valued diagram of auxiliary categories indexed by
ordinary lifts of one quotient object. -/
def quotientAuxiliaryDiagram (V : P.isoModSerre.Localization) : QuotientAuxiliaryLift P V ⥤
  Cat.{u,u} where
  obj A := Cat.of (AuxiliaryKernel P A.obj.left)
  map f := (auxiliaryPostcompose P f.hom.left
    (auxiliaryLift_hom_isoModSerre P.isoModSerre.Q V P f)).toCatHom
  map_id A := by
    apply Cat.Hom.ext
    exact auxiliaryPostcompose_id P A.obj.left
  map_comp f g := by
    apply Cat.Hom.ext
    exact auxiliaryPostcompose_comp P f.hom.left g.hom.left
      (auxiliaryLift_hom_isoModSerre P.isoModSerre.Q V P f)
      (auxiliaryLift_hom_isoModSerre P.isoModSerre.Q V P g)


/-- The comparison cocone into the actual isomorphism structured comma. -/
def quotientAuxiliaryCocone (V : P.isoModSerre.Localization) : Cocone (quotientAuxiliaryDiagram
  P V) where
  pt := Cat.of (IsoStructuredComma P
    (Q.of ((CategoryTheory.ExactCategory.abelianExactStructure
      P.isoModSerre.Localization)).deflation ((CategoryTheory.ExactCategory.abelianExactStructure
      P.isoModSerre.Localization)).inflation V))
  ι :=
    { app A := (auxiliaryToIsoStructuredWithBase P (asIso A.obj.hom)).toCatHom
      naturality A B f := by
        simp only [Functor.const_obj_map]
        apply Cat.Hom.ext
        exact auxiliaryToIsoStructuredWithBase_postcompose P f.hom.left
          (auxiliaryLift_hom_isoModSerre P.isoModSerre.Q V P f)
          (asIso A.obj.hom) (asIso B.obj.hom) (CostructuredArrow.w f.hom) }

/-- Every actual transition in the ordinary-lift diagram is a homotopy equivalence. -/
def quotientAuxiliaryTransitionHomotopyEquiv {V : P.isoModSerre.Localization}
    {A B : QuotientAuxiliaryLift P V} (f : A ⟶ B) :
    ContinuousMap.HomotopyEquiv
      (ClassifyingSpace ((quotientAuxiliaryDiagram P V).obj A))
      (ClassifyingSpace ((quotientAuxiliaryDiagram P V).obj B)) :=
  auxiliaryPostcomposeClassifyingHomotopyEquiv P f.hom.left
    (auxiliaryLift_hom_isoModSerre P.isoModSerre.Q V P f)

@[simp]
theorem quotientAuxiliaryTransitionHomotopyEquiv_toFun {V : P.isoModSerre.Localization}
    {A B : QuotientAuxiliaryLift P V} (f : A ⟶ B) :
    (quotientAuxiliaryTransitionHomotopyEquiv P f).toFun =
      (classifyingSpaceMap ((quotientAuxiliaryDiagram P V).map f).toFunctor).hom := rfl

end SerreLocalization
end Quillen
