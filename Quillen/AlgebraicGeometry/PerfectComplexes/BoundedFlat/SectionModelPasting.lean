/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionModelComposition
public import Quillen.Waldhausen.SmallModel.CoefficientPasting

/-!
# Original Model coefficient pasting

The four actual Model arrows and their original evaluation comparison isomorphisms retain the
strict source composition transport and the total normalized geometric target comparison.
-/
@[expose] public section

open Quillen.Waldhausen

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The actual target binary comparison, whiskered by original evaluation. -/
def boundedFlatAffineSectionModelTargetIso {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffineSectionEvaluationModelMap R).functor ⋙
      (boundedFlatAffineOriginalCoefficientModelMap (f ≫ g)).functor ≅
    ((boundedFlatAffineSectionEvaluationModelMap R).functor ⋙
      (boundedFlatAffineOriginalCoefficientModelMap f).functor) ⋙
        (boundedFlatAffineOriginalCoefficientModelMap g).functor :=
  isoWhiskerLeft (boundedFlatAffineSectionEvaluationModelMap R).functor
    (boundedFlatAffineOriginalCoefficientModelCompIso f g) ≪≫
  (Functor.associator (boundedFlatAffineSectionEvaluationModelMap R).functor
    (boundedFlatAffineOriginalCoefficientModelMap f).functor
    (boundedFlatAffineOriginalCoefficientModelMap g).functor).symm

/-- The original second coefficient comparison after strict source composition. -/
def boundedFlatAffineSectionModelFirstRouteIso {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffineSectionModelMap (f ≫ g)).functor ⋙
      (boundedFlatAffineSectionEvaluationModelMap T).functor ≅
    ((boundedFlatAffineSectionModelMap f).functor ⋙
      (boundedFlatAffineSectionEvaluationModelMap S).functor) ⋙
        (boundedFlatAffineOriginalCoefficientModelMap g).functor :=
  eqToIso (congrArg (fun k => k ⋙
    (boundedFlatAffineSectionEvaluationModelMap T).functor)
      (Quillen.CategoryTheory.StrictSections.underCocartesianReindex_comp
        boundedFlatAffineProjection f g)) ≪≫
  Functor.associator (boundedFlatAffineSectionModelMap f).functor
    (boundedFlatAffineSectionModelMap g).functor
    (boundedFlatAffineSectionEvaluationModelMap T).functor ≪≫
  isoWhiskerLeft (boundedFlatAffineSectionModelMap f).functor
    (boundedFlatAffineSectionEvaluationCoefficientIso g) ≪≫
  (Functor.associator (boundedFlatAffineSectionModelMap f).functor
    (boundedFlatAffineSectionEvaluationModelMap S).functor
    (boundedFlatAffineOriginalCoefficientModelMap g).functor).symm

/-- The original first coefficient comparison followed by actual target pullback. -/
def boundedFlatAffineSectionModelSecondRouteIso {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    ((boundedFlatAffineSectionModelMap f).functor ⋙
      (boundedFlatAffineSectionEvaluationModelMap S).functor) ⋙
        (boundedFlatAffineOriginalCoefficientModelMap g).functor ≅
    ((boundedFlatAffineSectionEvaluationModelMap R).functor ⋙
      (boundedFlatAffineOriginalCoefficientModelMap f).functor) ⋙
        (boundedFlatAffineOriginalCoefficientModelMap g).functor :=
  isoWhiskerRight (boundedFlatAffineSectionEvaluationCoefficientIso f)
    (boundedFlatAffineOriginalCoefficientModelMap g).functor

end Quillen.PerfectComplexes
