/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionModelCoherence

/-!
# Composition of the unchanged Model coefficient comparisons

The original coefficient isomorphisms satisfy the actual two-route equation after the existing
common-universe lifting. All original evaluator and normalization maps are retained.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open Quillen.CategoryTheory.GrothendieckSections
universe u
namespace Quillen.PerfectComplexes

/-- The original coefficient Model arrow uses the unchanged normalized geometric functor. -/
theorem boundedFlatAffineOriginalCoefficientModelMap_functor {R S : CommRingCat.{u}}
    (f : R ⟶ S) :
    (boundedFlatAffineOriginalCoefficientModelMap f).functor =
      smallModelFunctor (boundedFlatNormalizedPullback (Spec.map f)) := rfl

/-- The whole composition equation for the original Model components, using the actual
pseudofunctor interfaces so no large category aliases need to be re-inferred. -/
theorem boundedFlatAffineSectionEvaluationCoefficientIso_comp_app
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
        ((boundedFlatAffineSectionEvaluationCoefficientIso f).hom.app s).down) := by
  rw [boundedFlatAffineSectionEvaluationCoefficientIso_hom_app (f ≫ g) s,
    boundedFlatAffineSectionEvaluationCoefficientIso_hom_app g
      ((Quillen.CategoryTheory.StrictSections.underCocartesianReindex
        (Pseudofunctor.Grothendieck.forget boundedFlatAffinePseudofunctor) f).obj s),
    boundedFlatAffineSectionEvaluationCoefficientIso_hom_app f s]
  simp only [AsSmall.up_map_down]
  exact smallCoefficientIso_comp_app boundedFlatAffinePseudofunctor f g
    (Nf := boundedFlatNormalizedPullback (Spec.map f))
    (Ng := boundedFlatNormalizedPullback (Spec.map g))
    (Nfg := boundedFlatNormalizedPullback (Spec.map (f ≫ g)))
    (boundedFlatPullbackNormalizationIso (Spec.map f))
    (boundedFlatPullbackNormalizationIso (Spec.map g))
    (boundedFlatPullbackNormalizationIso (Spec.map (f ≫ g))) s

end Quillen.PerfectComplexes
