/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionModelFunctor
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionRestrictionZero
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.FullOpenSectionModel
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenDiagram

/-!
# The actual full-open section restriction as a Model map

The exact original section restriction retains the inherited whole chosen-zero section.
This constructs the actual pointwise Model arrow, with no coefficient or seed compatibility
hypothesis and no claim yet about the separately required coefficient square.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS Quillen.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The existing source diagram retains the literal original chosen section-zero object. -/
private theorem sourceModelZero (a : Under R) :
    ((boundedFlatAffineSectionOpenModelFunctor j).obj a).waldhausen.zero =
      boundedFlatAffineSectionZero a.right :=
  boundedFlatAffineSectionWaldhausen_zero a.right

/-- The original target Model has exactly its inherited full-open whole-section zero. -/
private theorem targetModelZero (a : Under R) :
    (boundedFlatAffineFullOpenSectionModel j a).waldhausen.zero =
      boundedFlatAffineFullOpenSectionZero j a := rfl

/-- Original exactness in the literal original pointwise Model structure fields. -/
private theorem modelExactField (a : Under R) :
    Quillen.Waldhausen.IsExact
      (boundedFlatAffineSectionOpenModel (inclusion j a)).waldhausen.cof
      (boundedFlatAffineSectionOpenModel (inclusion j a)).waldhausen.weq
      (boundedFlatAffineFullOpenSectionModel j a).waldhausen.cof
      (boundedFlatAffineFullOpenSectionModel j a).waldhausen.weq
      (boundedFlatAffineFullOpenSectionRestriction j a) :=
  boundedFlatAffineFullOpenSectionRestriction_exact j a

/-- Exactness stated over the same original source diagram object and typed functor. -/
private theorem modelDiagramExactField (a : Under R) :
    Quillen.Waldhausen.IsExact
      ((boundedFlatAffineSectionOpenModelFunctor j).obj a).waldhausen.cof
      ((boundedFlatAffineSectionOpenModelFunctor j).obj a).waldhausen.weq
      (boundedFlatAffineFullOpenSectionModel j a).waldhausen.cof
      (boundedFlatAffineFullOpenSectionModel j a).waldhausen.weq
      (boundedFlatAffineFullOpenSectionRestrictionModelFunctor j a) := by
  delta boundedFlatAffineFullOpenSectionRestrictionModelFunctor
  exact modelExactField j a

/-- Explicit original endpoint equations give the literal whole chosen-zero equality. -/
private theorem modelZeroField (a : Under R) :
    (boundedFlatAffineFullOpenSectionRestrictionModelFunctor j a).obj
        ((boundedFlatAffineSectionOpenModelFunctor j).obj a).waldhausen.zero =
      (boundedFlatAffineFullOpenSectionModel j a).waldhausen.zero := by
  rw [sourceModelZero j a, targetModelZero j a,
    boundedFlatAffineFullOpenSectionRestrictionModelFunctor_eq j a]
  exact boundedFlatAffineFullOpenSectionRestriction_sectionZero j a

/-- The actual restriction with its genuine exactness and inherited chosen-zero equality. -/
def boundedFlatAffineSectionFullOpenModelMap (a : Under R) :
    boundedFlatAffineSectionOpenModel (inclusion j a) ⟶
      boundedFlatAffineFullOpenSectionModel j a := by
  change (boundedFlatAffineSectionOpenModelFunctor j).obj a ⟶
    boundedFlatAffineFullOpenSectionModel j a
  exact {
    functor := boundedFlatAffineFullOpenSectionRestrictionModelFunctor j a
    exact := by exact modelDiagramExactField j a
    zero := by exact modelZeroField j a }

end Quillen.PerfectComplexes
