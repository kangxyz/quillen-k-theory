/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionEvaluationNormalization

/-!
# Original normalized section evaluation consumers

The original geometric pullback comparisons, coefficient transitions and chosen-zero
normalizations satisfy the actual two-route equation with scheme and source transports retained.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.CategoryTheory.StrictSections Quillen.CategoryTheory.GrothendieckSections
universe u
namespace Quillen.Tests.BoundedFlatEvaluationNormalization

/-- The literal original affine composition constraint retains the geometric `Spec` transport. -/
theorem geometric_composition {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffinePseudofunctor.mapComp f.toLoc g.toLoc).hom.toNatTrans =
      eqToHom (congrArg boundedFlatPerfectPullback (Spec.map_comp f g)) ≫
        (boundedFlatPerfectPullbackCompIso (Spec.map g) (Spec.map f)).hom :=
  boundedFlatAffinePseudofunctor_mapComp_hom f g

/-- The original identity constraint has the same geometric identity comparison. -/
theorem geometric_identity (R : CommRingCat.{u}) :
    (boundedFlatAffinePseudofunctor.mapId ⟨R⟩).hom.toNatTrans =
      eqToHom (congrArg boundedFlatPerfectPullback (Spec.map_id R)) ≫
        (boundedFlatPerfectPullbackIdIso (Spec R)).hom :=
  boundedFlatAffinePseudofunctor_mapId_hom R

/-- The exact existing named coefficient iso remains the original section transition. -/
theorem original_coefficient {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedFlatAffineSectionCoefficientIso f =
      originalCoefficientIso boundedFlatAffinePseudofunctor f :=
  boundedFlatAffineSectionCoefficientIso_eq f

/-- The normalized comparison retains the existing geometric binary comparison. -/
theorem normalized_geometric_composition {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffineNormalizedCoefficientCompIso f g).hom =
      eqToHom (congrArg boundedFlatNormalizedPullback (Spec.map_comp f g)) ≫
        (boundedFlatNormalizedPullbackCompIso (Spec.map g) (Spec.map f)).hom :=
  boundedFlatAffineNormalizedCoefficientCompIso_hom f g

/-- The two original coefficient routes agree after the actual chosen-zero normalizations. -/
theorem original_normalized_routes {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffineSectionNormalizedCoefficientIso (f ≫ g)).hom ≫
        whiskerLeft (boundedFlatAffineOriginalEvaluation R)
          (boundedFlatAffineNormalizedCoefficientCompIso f g).hom =
      eqToHom (congrArg (fun G => G ⋙ boundedFlatAffineOriginalEvaluation T)
        (underCocartesianReindex_comp boundedFlatAffineProjection f g)) ≫
          (normalizedCoefficientRouteIso boundedFlatAffinePseudofunctor f g
            (boundedFlatPullbackNormalizationIso (Spec.map f))
            (boundedFlatPullbackNormalizationIso (Spec.map g))).hom :=
  boundedFlatAffineSectionNormalizedCoefficientIso_comp_hom f g

end Quillen.Tests.BoundedFlatEvaluationNormalization
