/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Sections

/-! Original-map consumers of bounded-flat affine cocartesian sections. -/
@[expose] public section

open Quillen.PerfectComplexes

noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace QuillenTest.BoundedFlatSections

open Quillen

/-- The geometric input is the original coefficient pullback functor. -/
theorem original_pullback {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedFlatAffinePseudofunctor.map f.toLoc).toFunctor =
      boundedFlatPerfectPullback (Spec.map f) := boundedFlatAffinePseudofunctor_map f

/-- Restricting a section evaluates it at the literal composite coefficient arrow. -/
theorem original_reindex_object {R S T : CommRingCat.{u}} (f : R ⟶ S) (h : S ⟶ T)
    (s : BoundedFlatAffineSections R) :
    ((boundedFlatAffineSectionsMap f).obj s).obj.val.obj (Under.mk h) =
      s.obj.val.obj (Under.mk (f ≫ h)) := rfl

/-- Restricting a vertical transformation preserves its actual component. -/
theorem original_reindex_morphism {R S T : CommRingCat.{u}} (f : R ⟶ S) (h : S ⟶ T)
    {s t : BoundedFlatAffineSections R} (a : s ⟶ t) :
    ((boundedFlatAffineSectionsMap f).map a).hom.val.app (Under.mk h) =
      a.hom.val.app (Under.mk (f ≫ h)) := rfl

/-- Evaluation retains the section's original identity component in the total category. -/
theorem original_evaluation (R : CommRingCat.{u}) (s : BoundedFlatAffineSections R) :
    ((boundedFlatAffineSectionsEvaluation R).obj s).val =
      s.obj.val.obj (Under.mk (𝟙 R)) := rfl

/-- Coefficient identity is literal at the section-category level. -/
theorem strict_identity (R : CommRingCat.{u}) :
    boundedFlatAffineSectionsMap (𝟙 R) = 𝟭 (BoundedFlatAffineSections R) :=
  Quillen.CategoryTheory.StrictSections.underCocartesianReindex_id
    boundedFlatAffineProjection R

/-- Two coefficient maps compose literally at the section-category level. -/
theorem strict_composition {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    boundedFlatAffineSectionsMap (f ≫ g) =
      boundedFlatAffineSectionsMap f ⋙ boundedFlatAffineSectionsMap g :=
  Quillen.CategoryTheory.StrictSections.underCocartesianReindex_comp
    boundedFlatAffineProjection f g

/-- Every section transition is required to be an actual strongly cocartesian lift. -/
theorem original_cocartesian (R : CommRingCat.{u}) (s : BoundedFlatAffineSections R)
    {i j : Under R} (a : i ⟶ j) :
    boundedFlatAffineProjection.IsStronglyCocartesian a.right (s.obj.val.map a) :=
  s.property a

end QuillenTest.BoundedFlatSections
