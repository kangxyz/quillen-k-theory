/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.CategoryTheory.FiberedCategory.GrothendieckSectionEquivalence
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

/-!
# Pointwise chosen-zero sections of a Grothendieck projection

A family of actual chosen zero objects preserved by the original transition functors defines
one global section. Its restriction to every coslice uses the same chosen fiber zeros.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
universe u v u' v'
namespace Quillen.CategoryTheory.GrothendieckZeroSections
variable {C : Type u} [Category.{v} C]
  (F : Pseudofunctor (LocallyDiscrete C) Cat.{v', u'})
  (z : ∀ R : C, F.obj ⟨R⟩) (hz : ∀ R, IsZero (z R))
  (hm : ∀ {R S : C} (f : R ⟶ S), IsZero ((F.map f.toLoc).toFunctor.obj (z R)))

/-- The global zero section uses the specified zero in each original fiber. -/
def globalSection : C ⥤ Pseudofunctor.Grothendieck F where
  obj R := ⟨R, z R⟩
  map {_ S} f := ⟨f, (hz S).from_ _⟩
  map_id R := Pseudofunctor.Grothendieck.Hom.ext _ _ rfl ((hz R).eq_of_tgt _ _)
  map_comp {_ _ T} _ _ :=
    Pseudofunctor.Grothendieck.Hom.ext _ _ rfl ((hz T).eq_of_tgt _ _)

instance instIsHomLift {R S : C} (f : R ⟶ S) :
    (Pseudofunctor.Grothendieck.forget F).IsHomLift f
      ((globalSection F z hz).map f) :=
  IsHomLift.map (Pseudofunctor.Grothendieck.forget F) ((globalSection F z hz).map f)

include hm in
/-- Every original zero transition is strongly cocartesian by zero-object uniqueness. -/
theorem isStronglyCocartesian {R S : C} (f : R ⟶ S) :
    (Pseudofunctor.Grothendieck.forget F).IsStronglyCocartesian f
      ((globalSection F z hz).map f) where
  universal_property' {y} g φ hφ := by
    let ψ : (globalSection F z hz).obj S ⟶ y := ⟨g, (hm g).to_ _⟩
    have hψ : (Pseudofunctor.Grothendieck.forget F).IsHomLift g ψ := IsHomLift.map _ ψ
    refine ⟨ψ, ⟨hψ, ?_⟩, ?_⟩
    · refine Pseudofunctor.Grothendieck.Hom.ext _ _ ?_ ?_
      · simpa [globalSection, ψ] using
          IsHomLift.fac (Pseudofunctor.Grothendieck.forget F) (f ≫ g) φ
      · exact (hm φ.base).eq_of_src _ _
    rintro χ ⟨hχ, _⟩
    obtain ⟨rfl⟩ : g = χ.base := by
      simpa using IsHomLift.fac (Pseudofunctor.Grothendieck.forget F) g χ
    exact Pseudofunctor.Grothendieck.Hom.ext _ _ rfl ((hm χ.base).eq_of_src _ _)

/-- The global section is literally over the identity of the base. -/
theorem globalSection_comp :
    globalSection F z hz ⋙ Pseudofunctor.Grothendieck.forget F = 𝟭 C := rfl

/-- The chosen-zero section over a coslice is the restriction of the one global section. -/
def sectionZero (R : C) :
    StrictSections.underCocartesian (Pseudofunctor.Grothendieck.forget F) R :=
  ⟨⟨Under.forget R ⋙ globalSection F z hz, rfl⟩, fun _ _ f =>
    isStronglyCocartesian F z hz hm f.right⟩

/-- Evaluation retains the original chosen zero literally. -/
theorem originalEvaluation_sectionZero (R : C) :
    (GrothendieckSections.originalEvaluation F R).obj (sectionZero F z hz hm R) = z R := rfl

/-- Restriction retains the pointwise chosen-zero section literally. -/
theorem reindex_sectionZero {R S : C} (f : R ⟶ S) :
    (StrictSections.underCocartesianReindex (Pseudofunctor.Grothendieck.forget F) f).obj
      (sectionZero F z hz hm R) = sectionZero F z hz hm S := rfl

/-- The pointwise section is genuinely a zero object, by the proved faithful full evaluation. -/
theorem isZero_sectionZero (R : C) : IsZero (sectionZero F z hz hm R) :=
  IsZero.of_full_of_faithful_of_isZero (GrothendieckSections.originalEvaluation F R) _ (hz R)

end Quillen.CategoryTheory.GrothendieckZeroSections
