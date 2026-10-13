/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionModel
public import Quillen.CategoryTheory.FiberedCategory.GrothendieckUnderRestrictionNaturality

/-!
# The original full-open section restriction as a coefficient transformation

The pointwise exact Model arrows retain their actual chosen zeros and commute with every
original coefficient reindexing. Applying the same iterated-S functor gives the actual
restriction transformation of prespectrum diagrams, without a compactness hypothesis.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]
attribute [local irreducible] boundedFlatPerfectPseudofunctor
  boundedFlatAffineFullOpenPseudofunctor boundedFlatAffineFullOpenRestrictionStrongTrans

/-- The original chosen-zero Model restriction commutes with every original coefficient arrow. -/
theorem boundedFlatAffineSectionFullOpenModelMap_naturality {a b : Under R} (f : a ⟶ b) :
    (boundedFlatAffineSectionOpenModelFunctor j).map f ≫
        boundedFlatAffineSectionFullOpenModelMap j b =
      boundedFlatAffineSectionFullOpenModelMap j a ≫
        (boundedFlatAffineFullOpenSectionModelFunctor j).map f := by
  apply Model.Hom.ext
  exact Quillen.CategoryTheory.GrothendieckUnderRestriction.sectionFunctor_naturality
    Scheme.Spec.rightOp boundedFlatPerfectPseudofunctor R
    (boundedFlatAffineFullOpenPseudofunctor j)
    (boundedFlatAffineFullOpenRestrictionStrongTrans j) f

/-- The actual restriction arrows form a strict transformation of the same Model diagrams. -/
def boundedFlatAffineSectionFullOpenModelTransformation :
    boundedFlatAffineSectionOpenModelFunctor j ⟶
      boundedFlatAffineFullOpenSectionModelFunctor j where
  app a := boundedFlatAffineSectionFullOpenModelMap j a
  naturality a b f := by
    apply Model.Hom.ext
    exact Quillen.CategoryTheory.GrothendieckUnderRestriction.sectionFunctor_naturality
      Scheme.Spec.rightOp boundedFlatPerfectPseudofunctor R
      (boundedFlatAffineFullOpenPseudofunctor j)
      (boundedFlatAffineFullOpenRestrictionStrongTrans j) f

/-- Original realization retains the unchanged full-open restriction coefficient square. -/
def boundedFlatAffineSectionFullOpenPrespectrumTransformation :
    boundedFlatAffineSectionOpenPrespectrumFunctor j ⟶
      boundedFlatAffineFullOpenSectionPrespectrumFunctor j :=
  Functor.whiskerRight (boundedFlatAffineSectionFullOpenModelTransformation j) prespectrumFunctor

/-- Every component is exactly the existing original full-open section restriction map. -/
theorem boundedFlatAffineSectionFullOpenPrespectrumTransformation_app (a : Under R) :
    (boundedFlatAffineSectionFullOpenPrespectrumTransformation j).app a =
      prespectrumMap (boundedFlatAffineSectionFullOpenModelMap j a) := rfl

end Quillen.PerfectComplexes
