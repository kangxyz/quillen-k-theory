/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionForgetExact
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedSectionDiagram
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionPrespectrum

/-!
# The original support-forgetting Model and prespectrum maps

The actual full-subcategory inclusion is exact and preserves the chosen section zero literally.
The original coefficient forget squares therefore give a strict natural transformation from
the fixed-open supported diagram to the ambient section diagram restricted along Under.forget.
This is an inclusion toward localization, with no equivalence or localization assertion.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
open Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original support-forgetting functor with its proved exactness and literal chosen zero. -/
def boundedFlatAffineSupportedSectionForgetModelMap :
    boundedFlatAffineSupportedSectionModel j ⟶ boundedFlatAffineSectionModel R where
  functor := (boundedFlatAffineSectionSupported j).ι
  exact := boundedFlatAffineSupportedSectionForget_exact j
  zero := boundedFlatAffineSupportedSectionForget_zero j

/-- Forgetting support commutes with each original specified coefficient/open-pair square. -/
theorem boundedFlatAffineSupportedSectionForgetModelMap_naturality
    {S : CommRingCat.{u}} {V : Scheme.{u}} (j' : V ⟶ Spec S) [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f) :
    boundedFlatAffineSupportedSectionModelMap j j' f l h ≫
        boundedFlatAffineSupportedSectionForgetModelMap j' =
      boundedFlatAffineSupportedSectionForgetModelMap j ≫ boundedFlatAffineSectionModelMap f := by
  apply Model.Hom.ext
  exact boundedFlatAffineSupportedSectionsMap_forget j j' f l h

/-- Actual support inclusion is strictly natural on the original fixed-pullback diagram. -/
def boundedFlatAffineSupportedSectionForgetModelTransformation :
    boundedFlatAffineSupportedSectionModelFunctor j ⟶
      Under.forget R ⋙ boundedFlatAffineSectionModelFunctor where
  app a := boundedFlatAffineSupportedSectionForgetModelMap (inclusion j a)
  naturality _ _ f := boundedFlatAffineSupportedSectionForgetModelMap_naturality
    (inclusion j _) (inclusion j _) f.right (openMap j f) (openMap_inclusion j f)

/-- The actual iterated-S support-forgetting prespectrum arrow. -/
def boundedFlatAffineSupportedSectionForgetPrespectrumMap :
    prespectrum (boundedFlatAffineSupportedSectionModel j) ⟶
      prespectrum (boundedFlatAffineSectionModel R) :=
  prespectrumMap (boundedFlatAffineSupportedSectionForgetModelMap j)

/-- Apply the original prespectrum functor to the actual strict Model natural transformation. -/
def boundedFlatAffineSupportedSectionForgetPrespectrumTransformation :
    boundedFlatAffineSupportedSectionPrespectrumFunctor j ⟶
      Under.forget R ⋙ boundedFlatAffineSectionPrespectrumFunctor :=
  Functor.whiskerRight (boundedFlatAffineSupportedSectionForgetModelTransformation j)
    prespectrumFunctor

/-- Its components are exactly the original support-forgetting iterated-S maps. -/
theorem boundedFlatAffineSupportedSectionForgetPrespectrumTransformation_app (a : Under R) :
    (boundedFlatAffineSupportedSectionForgetPrespectrumTransformation j).app a =
      boundedFlatAffineSupportedSectionForgetPrespectrumMap (inclusion j a) := rfl

end Quillen.PerfectComplexes
