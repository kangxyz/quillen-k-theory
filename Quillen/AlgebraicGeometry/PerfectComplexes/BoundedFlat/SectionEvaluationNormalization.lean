/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.PseudofunctorCoherence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NormalizedPullbackCoherence
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionSpectrumNaturality
public import Quillen.Aglib.CategoryTheory.FiberedCategory.CocartesianEvaluationNormalization

/-!
# Actual normalized geometric comparisons for section evaluation

The target normalization is the same chosen-zero normalization used by the original geometric
prespectrum maps. Its composition constraint retains the actual affine pseudofunctor constraint.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.CategoryTheory.GrothendieckSections
universe u
namespace Quillen.PerfectComplexes

/-- The original named geometric coefficient iso is the actual section transition iso. -/
theorem boundedFlatAffineSectionCoefficientIso_eq {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedFlatAffineSectionCoefficientIso f =
      originalCoefficientIso boundedFlatAffinePseudofunctor f := by
  rfl

/-- The actual coefficient transition followed by the unchanged original normalization. -/
def boundedFlatAffineSectionNormalizedCoefficientIso {R S : CommRingCat.{u}} (f : R ⟶ S) :
    boundedFlatAffineSectionsMap f ⋙ boundedFlatAffineOriginalEvaluation S ≅
      boundedFlatAffineOriginalEvaluation R ⋙ boundedFlatNormalizedPullback (Spec.map f) :=
  normalizedCoefficientIso boundedFlatAffinePseudofunctor f
    (boundedFlatPullbackNormalizationIso (Spec.map f))

/-- The composition constraint uses the three actual original pullback normalizations. -/
def boundedFlatAffineNormalizedCoefficientCompIso {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    boundedFlatNormalizedPullback (Spec.map (f ≫ g)) ≅
      boundedFlatNormalizedPullback (Spec.map f) ⋙ boundedFlatNormalizedPullback (Spec.map g) :=
  normalizedCoefficientCompIso boundedFlatAffinePseudofunctor f g
    (boundedFlatPullbackNormalizationIso (Spec.map f))
    (boundedFlatPullbackNormalizationIso (Spec.map g))
    (boundedFlatPullbackNormalizationIso (Spec.map (f ≫ g)))

private theorem normalizationIso_transport {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (h : f = g) :
    (boundedFlatPullbackNormalizationIso f).inv ≫
        eqToHom (congrArg boundedFlatPerfectPullback h) =
      eqToHom (congrArg boundedFlatNormalizedPullback h) ≫
        (boundedFlatPullbackNormalizationIso g).inv := by
  subst h
  simp

/-- The normalized affine constraint is exactly the original geometric comparison, including
its actual scheme-map equality transport. -/
theorem boundedFlatAffineNormalizedCoefficientCompIso_hom {R S T : CommRingCat.{u}}
    (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffineNormalizedCoefficientCompIso f g).hom =
      eqToHom (congrArg boundedFlatNormalizedPullback (Spec.map_comp f g)) ≫
        (boundedFlatNormalizedPullbackCompIso (Spec.map g) (Spec.map f)).hom := by
  simp only [boundedFlatAffineNormalizedCoefficientCompIso, normalizedCoefficientCompIso,
    boundedFlatNormalizedPullbackCompIso, Iso.trans_hom, Iso.symm_hom,
    Cat.Hom.toNatIso_hom, boundedFlatAffinePseudofunctor_mapComp_hom,
    isoWhiskerRight_hom, isoWhiskerLeft_hom, Category.assoc]
  rw [reassoc_of% normalizationIso_transport (Spec.map_comp f g)]
  rfl

/-- The two normalized coefficient tracks are governed by the proved section composition law. -/
theorem boundedFlatAffineSectionNormalizedCoefficientIso_comp_hom
    {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffineSectionNormalizedCoefficientIso (f ≫ g)).hom ≫
        whiskerLeft (boundedFlatAffineOriginalEvaluation R)
          (boundedFlatAffineNormalizedCoefficientCompIso f g).hom =
      eqToHom (congrArg (fun G => G ⋙ boundedFlatAffineOriginalEvaluation T)
        (Quillen.CategoryTheory.StrictSections.underCocartesianReindex_comp
          boundedFlatAffineProjection f g)) ≫
          (normalizedCoefficientRouteIso boundedFlatAffinePseudofunctor f g
            (boundedFlatPullbackNormalizationIso (Spec.map f))
            (boundedFlatPullbackNormalizationIso (Spec.map g))).hom :=
  normalizedCoefficientIso_comp_hom boundedFlatAffinePseudofunctor f g
    (boundedFlatPullbackNormalizationIso (Spec.map f))
    (boundedFlatPullbackNormalizationIso (Spec.map g))
    (boundedFlatPullbackNormalizationIso (Spec.map (f ≫ g)))

end Quillen.PerfectComplexes
