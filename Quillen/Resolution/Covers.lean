/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Basic
public import Quillen.Resolution.QCalculus
public import Quillen.Topology.ClassifyingSpace.Equivalence

/-!
# Admissible resolving covers and their contraction

The objects are actual admissible epimorphisms onto a fixed object, with
source in the resolving subcategory. Morphisms are admissible epimorphisms
commuting with the augmentations. Pullback against one chosen cover gives
the contraction needed in the length-one resolution theorem.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe v u
open CategoryTheory CategoryTheory.Limits

namespace Quillen.Resolution
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteBiproducts C]
  (E : ExactStructure C) (P : ObjectProperty C) (M : C)

/-- An actual admissible epimorphism from a resolving object. -/
structure Cover where
  /-- The resolving source object of the cover, required to satisfy `P`. -/
  obj : C
  property : P obj
  /-- The admissible epimorphism from the resolving source onto `M`. -/
  hom : obj ⟶ M
  admissible : E.deflation hom

namespace Cover
variable {E P M}

/-- Cover comparisons are themselves admissible epimorphisms. -/
@[ext] structure Hom (X Y : Cover E P M) where
  /-- The admissible epimorphism between cover sources that commutes with their maps to `M`. -/
  hom : X.obj ⟶ Y.obj
  admissible : E.deflation hom
  w : hom ≫ Y.hom = X.hom

instance : Category (Cover E P M) where
  Hom := Hom
  id X := ⟨𝟙 X.obj, E.deflation_id _, by simp⟩
  comp f g := ⟨f.hom ≫ g.hom, E.deflation_comp _ _ f.admissible g.admissible,
    by rw [Category.assoc, g.w, f.w]⟩
  id_comp _ := Hom.ext (by simp)
  comp_id _ := Hom.ext (by simp)
  assoc _ _ _ := Hom.ext (by simp [Category.assoc])

@[simp] lemma id_hom (X : Cover E P M) : (𝟙 X : X ⟶ X).hom = 𝟙 X.obj := rfl
@[simp] lemma comp_hom {X Y Z : Cover E P M} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

variable [E.IsExtensionClosed P] [E.IsAdmissibleSubobjectClosed P]

/-- A pullback of two resolving covers is again a resolving cover. Its kernel
is an admissible subobject of the first resolving source. -/
lemma pullback_mem (X Y : Cover E P M) [HasPullback X.hom Y.hom] :
    P (pullback X.hom Y.hom) := by
  obtain ⟨K, i, hi, hS⟩ := X.admissible
  exact E.prop_pullback P hS
    (E.prop_of_inflation P i (E.inflation_of_conflation hS) X.property)
    Y.property Y.hom

instance hasPullback (X Y : Cover E P M) : HasPullback X.hom Y.hom :=
  E.deflation.hasPullback Y.hom X.admissible

/-- Common refinement by the categorical pullback. -/
def pullback (X Y : Cover E P M) : Cover E P M where
  obj := Limits.pullback X.hom Y.hom
  property := pullback_mem X Y
  hom := Limits.pullback.fst X.hom Y.hom ≫ X.hom
  admissible := E.deflation_comp _ _
    (E.deflation.pullback_fst _ _ Y.admissible) X.admissible

/-- First common-refinement projection. -/
def fst (X Y : Cover E P M) : pullback X Y ⟶ X :=
  ⟨Limits.pullback.fst _ _, E.deflation.pullback_fst _ _ Y.admissible, rfl⟩

/-- Second common-refinement projection. -/
def snd (X Y : Cover E P M) : pullback X Y ⟶ Y :=
  ⟨Limits.pullback.snd _ _, E.deflation.pullback_snd _ _ X.admissible,
    Limits.pullback.condition.symm⟩

omit [E.IsExtensionClosed P] [E.IsAdmissibleSubobjectClosed P] in
/-- The induced map of pullbacks is a base change of the original cover map. -/
lemma map_isPullback {X Y : Cover E P M} (f : X ⟶ Y) (B : Cover E P M) :
    IsPullback
      (Limits.pullback.map X.hom B.hom Y.hom B.hom f.hom (𝟙 _) (𝟙 _)
        (by simpa using f.w.symm) (by simp))
      (Limits.pullback.fst X.hom B.hom)
      (Limits.pullback.fst Y.hom B.hom) f.hom := by
  apply IsPullback.of_right
    (t := (IsPullback.of_hasPullback Y.hom B.hom).flip)
  · simpa [f.w] using (IsPullback.of_hasPullback X.hom B.hom).flip
  · simp

/-- Functorial common refinement against a fixed cover. -/
def refinement (B : Cover E P M) : Cover E P M ⥤ Cover E P M where
  obj X := pullback X B
  map {X Y} f :=
    { hom := Limits.pullback.map X.hom B.hom Y.hom B.hom f.hom (𝟙 _) (𝟙 _)
        (by simpa using f.w.symm) (by simp)
      admissible := E.deflation.of_isPullback (map_isPullback f B).flip f.admissible
      w := by
        change _ ≫ (Limits.pullback.fst Y.hom B.hom ≫ Y.hom) =
          Limits.pullback.fst X.hom B.hom ≫ X.hom
        simp only [← Category.assoc, Limits.pullback.lift_fst]
        simp only [Category.assoc, f.w] }
  map_id X := by
    apply Hom.ext
    dsimp
    apply Limits.pullback.hom_ext <;> simp [pullback]
  map_comp f g := by
    apply Hom.ext
    apply Limits.pullback.hom_ext <;> simp [Category.assoc]

/-- Refinement projects naturally onto the original cover. -/
def refinementToId (B : Cover E P M) : refinement B ⟶ 𝟭 (Cover E P M) where
  app X := fst X B
  naturality {X Y} f := by apply Hom.ext; simp [refinement, fst]

/-- Refinement also projects naturally onto the chosen cover. -/
def refinementToConst (B : Cover E P M) :
    refinement B ⟶ (Functor.const (Cover E P M)).obj B where
  app X := snd X B
  naturality {X Y} f := by apply Hom.ext; simp [refinement, snd]

/-- The category of covers is genuinely contractible: its identity is joined
to a constant by the explicit pullback-refinement zigzag. -/
theorem contractible (B : Cover E P M) :
    ContractibleSpace (ClassifyingSpace (Cover E P M)) := by
  apply (contractible_iff_id_nullhomotopic _).2
  refine ⟨classifyingSpacePoint B, ?_⟩
  have h₁ := (classifyingSpaceNaturalTransformationHomotopy (refinementToId B)).symm
  have h₂ := classifyingSpaceNaturalTransformationHomotopy (refinementToConst B)
  simpa only [classifyingSpaceMap_id, TopCat.hom_id, classifyingSpaceMap_const] using
    (ContinuousMap.Homotopic.trans ⟨h₁⟩ ⟨h₂⟩)

end Cover
end Quillen.Resolution
