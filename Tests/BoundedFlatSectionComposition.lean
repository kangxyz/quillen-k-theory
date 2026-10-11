/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Pseudofunctor
public import Quillen.CategoryTheory.FiberedCategory.CocartesianSectionComposition

/-!
# Actual bounded-flat section coefficient composition

These consumers use genuine bounded-flat sections and their original pullback evaluation
components. The original geometric pseudofunctor comparison is retained explicitly.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.CategoryTheory.GrothendieckSections
universe u
namespace Quillen.Tests.BoundedFlatSectionComposition

/-- The actual bounded-flat pseudofunctor retains the original two-coefficient triangle. -/
theorem original_coefficient_triangle {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T)
    (s : Quillen.CategoryTheory.StrictSections.underCocartesian
      (Pseudofunctor.Grothendieck.forget boundedFlatAffinePseudofunctor) R) :
    originalTransition boundedFlatAffinePseudofunctor R s (Under.mk (f ≫ g)) =
      (boundedFlatAffinePseudofunctor.mapComp f.toLoc g.toLoc).hom.toNatTrans.app
          ((originalEvaluation boundedFlatAffinePseudofunctor R).obj s) ≫
        (boundedFlatAffinePseudofunctor.map g.toLoc).toFunctor.map
          (originalTransition boundedFlatAffinePseudofunctor R s (Under.mk f)) ≫
        originalArrowTransition boundedFlatAffinePseudofunctor R s
          (Under.homMk g : Under.mk f ⟶ Under.mk (f ≫ g)) :=
  originalTransition_comp boundedFlatAffinePseudofunctor R f g s

/-- The actual geometric unit comparison occurs at every identity arrow. -/
theorem original_identity (R : CommRingCat.{u})
    (s : Quillen.CategoryTheory.StrictSections.underCocartesian
      (Pseudofunctor.Grothendieck.forget boundedFlatAffinePseudofunctor) R) (j : Under R) :
    originalArrowTransition boundedFlatAffinePseudofunctor R s (𝟙 j) =
      (boundedFlatAffinePseudofunctor.mapId ⟨j.right⟩).hom.toNatTrans.app
        ((originalEvaluationAt boundedFlatAffinePseudofunctor R j).obj s) :=
  originalArrowTransition_id boundedFlatAffinePseudofunctor R s j

/-- Every original coefficient arrow is retained under strict restriction. -/
theorem original_restriction {R S : CommRingCat.{u}} (f : R ⟶ S)
    (s : Quillen.CategoryTheory.StrictSections.underCocartesian
      (Pseudofunctor.Grothendieck.forget boundedFlatAffinePseudofunctor) R)
    {j k : Under S} (a : j ⟶ k) :
    originalArrowTransition boundedFlatAffinePseudofunctor S
        ((Quillen.CategoryTheory.StrictSections.underCocartesianReindex
          (Pseudofunctor.Grothendieck.forget boundedFlatAffinePseudofunctor) f).obj s) a =
      originalArrowTransition boundedFlatAffinePseudofunctor R s ((Under.map f).map a) :=
  originalArrowTransition_reindex boundedFlatAffinePseudofunctor R f s a

/-- The genuine evaluation isomorphism retains the original extracted component. -/
theorem original_component (R : CommRingCat.{u})
    (s : Quillen.CategoryTheory.StrictSections.underCocartesian
      (Pseudofunctor.Grothendieck.forget boundedFlatAffinePseudofunctor) R) (j : Under R) :
    (originalEvaluationTransitionIso boundedFlatAffinePseudofunctor R j).hom.app s =
      originalTransition boundedFlatAffinePseudofunctor R s j :=
  originalEvaluationTransitionIso_hom_app boundedFlatAffinePseudofunctor R s j

end Quillen.Tests.BoundedFlatSectionComposition
