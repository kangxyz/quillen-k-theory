/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionModelComposition

/-!
# Original Model coefficient composition consumers

The unchanged coefficient components satisfy their actual source-transport equation. The total
binary comparison still evaluates to the original geometric normalization and `Spec` transport.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.CategoryTheory.GrothendieckSections
universe u
namespace Quillen.Tests.BoundedFlatModelComposition

/-- The original three coefficient comparisons obey the complete pointwise composition law. -/
theorem original_coefficient_routes
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (s : BoundedFlatAffineSections R) :
    (boundedFlatAffineSectionEvaluationCoefficientIso (f ≫ g)).hom.app s ≫
        (AsSmall.up.{u, u+1, 0}).map
          ((normalizedCoefficientCompIso boundedFlatAffinePseudofunctor f g
            (boundedFlatPullbackNormalizationIso (Spec.map f))
            (boundedFlatPullbackNormalizationIso (Spec.map g))
            (boundedFlatPullbackNormalizationIso (Spec.map (f ≫ g)))).hom.app
              ((originalEvaluation boundedFlatAffinePseudofunctor R).obj s)) =
      (eqToHom (congrArg
        (fun G => G ⋙ (originalEvaluation boundedFlatAffinePseudofunctor T ⋙
          AsSmall.up.{u, u+1, 0}))
        (Quillen.CategoryTheory.StrictSections.underCocartesianReindex_comp
          (Pseudofunctor.Grothendieck.forget boundedFlatAffinePseudofunctor) f g))).app s ≫
      (boundedFlatAffineSectionEvaluationCoefficientIso g).hom.app
        ((Quillen.CategoryTheory.StrictSections.underCocartesianReindex
          (Pseudofunctor.Grothendieck.forget boundedFlatAffinePseudofunctor) f).obj s) ≫
      AsSmall.up.map ((boundedFlatNormalizedPullback (Spec.map g)).map
        ((boundedFlatAffineSectionEvaluationCoefficientIso f).hom.app s).down) :=
  boundedFlatAffineSectionEvaluationCoefficientIso_comp_app f g s

/-- The original coefficient Model map retains its actual normalized functor. -/
theorem original_coefficient_functor {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedFlatAffineOriginalCoefficientModelMap f).functor =
      smallModelFunctor (boundedFlatNormalizedPullback (Spec.map f)) :=
  boundedFlatAffineOriginalCoefficientModelMap_functor f

/-- The total normalized comparison retains the original geometric `Spec` transport. -/
theorem original_binary_comparison {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffineNormalizedCoefficientCompIso f g).hom =
      eqToHom (congrArg boundedFlatNormalizedPullback (Spec.map_comp f g)) ≫
        (boundedFlatNormalizedPullbackCompIso (Spec.map g) (Spec.map f)).hom :=
  boundedFlatAffineNormalizedCoefficientCompIso_hom f g

end Quillen.Tests.BoundedFlatModelComposition
