/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Actual bounded-above complexes and their ambient derived objects

The full category retains original cochain complexes and chain maps. The canonical
functor to the ambient bounded-above derived category inverts original quasi-isomorphisms
and is essentially surjective through actual strictly bounded representatives.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w
open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace Quillen.CochainComplex

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- Actual bounded-above cochain complexes, with their original chain maps. -/
def boundedAbove : ObjectProperty (CochainComplex C ℤ) := fun K => ∃ b, K.IsStrictlyLE b

abbrev BoundedAboveComplex := (boundedAbove C).FullSubcategory

variable {C}

def chosenUpperBound (K : BoundedAboveComplex C) : ℤ := K.property.choose

instance chosenUpperBound_spec (K : BoundedAboveComplex C) :
    K.obj.IsStrictlyLE (chosenUpperBound K) := K.property.choose_spec

variable (C) [HasDerivedCategory.{w} C]

/-- The canonical functor from actual bounded-above complexes to the ambient bounded-above derived category. -/
def boundedAboveQMinus : BoundedAboveComplex C ⥤ DerivedCategory.Minus C :=
  (DerivedCategory.TStructure.t.minus).lift ((boundedAbove C).ι ⋙ DerivedCategory.Q)
    (fun K => ⟨chosenUpperBound K, by
      change (DerivedCategory.Q.obj K.obj).IsLE (chosenUpperBound K)
      infer_instance⟩)

/-- Every object in the ambient bounded-above derived category has an actual
bounded-above complex representative, without assuming enough projectives or injectives. -/
instance boundedAboveQMinus_essSurj : (boundedAboveQMinus C).EssSurj where
  mem_essImage X := by
    obtain ⟨b, hb⟩ := X.property
    let : X.obj.IsLE b := hb
    obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isLE X.obj b
    exact ⟨⟨K, b, hK⟩, ⟨ObjectProperty.isoMk _ e.symm⟩⟩

/-- The canonical functor inverts original quasi-isomorphisms. -/
theorem boundedAboveQMinus_inverts {K L : BoundedAboveComplex C} (f : K ⟶ L)
    [QuasiIso f.hom] : IsIso ((boundedAboveQMinus C).map f) := by
  have : IsIso ((DerivedCategory.Minus.ι : DerivedCategory.Minus C ⥤ _).map
      ((boundedAboveQMinus C).map f)) := by
    change IsIso (DerivedCategory.Q.map f.hom)
    infer_instance
  exact isIso_of_reflects_iso _ (DerivedCategory.Minus.ι : DerivedCategory.Minus C ⥤ _)

end Quillen.CochainComplex
