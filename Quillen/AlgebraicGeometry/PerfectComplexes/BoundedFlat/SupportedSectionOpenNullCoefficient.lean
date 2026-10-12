/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionOpenDiagram
public import Quillen.Waldhausen.SConstruction.Iterated.PrespectrumZeroNaturality

/-!
# Coefficient naturality of the original support-to-relative-open null track

The unchanged support inclusions and fine-to-coarse maps give an actual strict Model square
for every specified commuting affine open-pair square. Uniqueness from the inherited zero
identifies the original weak transformations, so their full reversed realization tracks agree
at the identical time. This includes the original degree-zero loop and all structure coordinates.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R S : CommRingCat.{u}} {U V : Scheme.{u}}
    (j : U ⟶ Spec R) (j' : V ⟶ Spec S) [IsOpenImmersion j] [IsOpenImmersion j']
    (f : R ⟶ S) (l : V ⟶ U) (h : l ≫ j = j' ≫ Spec.map f)

/-- The exact original support/coarse coefficient square is literal on the chosen-zero Models. -/
theorem boundedFlatAffineSupportedSectionOpenModelSquare :
    (boundedFlatAffineSupportedSectionForgetModelMap j ≫
      boundedFlatAffineSectionOpenModelMap j) ≫
        boundedFlatAffineSectionOpenReindexModelMap j j' f l h =
      boundedFlatAffineSupportedSectionModelMap j j' f l h ≫
        (boundedFlatAffineSupportedSectionForgetModelMap j' ≫
          boundedFlatAffineSectionOpenModelMap j') := by
  calc
    _ = boundedFlatAffineSupportedSectionForgetModelMap j ≫
        (boundedFlatAffineSectionModelMap f ≫ boundedFlatAffineSectionOpenModelMap j') :=
      (Category.assoc _ _ _).trans
        (congrArg (fun k => boundedFlatAffineSupportedSectionForgetModelMap j ≫ k)
          (boundedFlatAffineSectionOpenModelMap_naturality j j' f l h).symm)
    _ = (boundedFlatAffineSupportedSectionModelMap j j' f l h ≫
        boundedFlatAffineSupportedSectionForgetModelMap j') ≫
          boundedFlatAffineSectionOpenModelMap j' :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (fun k => k ≫ boundedFlatAffineSectionOpenModelMap j')
          (boundedFlatAffineSupportedSectionForgetModelMap_naturality j j' f l h).symm)
    _ = _ := Category.assoc _ _ _

/-- Every original null-cylinder value commutes with the actual coefficient map at the same time. -/
theorem boundedFlatAffineSupportedSectionOpenNullHomotopy_coefficient
    (n : ℕ) (s : unitInterval)
    (x : (prespectrum (boundedFlatAffineSupportedSectionModel j)).space n) :
    (boundedFlatAffineSectionOpenReindexPrespectrumMap j j' f l h).map n
        ((boundedFlatAffineSupportedSectionOpenNullHomotopy j).level n (s, x)) =
      (boundedFlatAffineSupportedSectionOpenNullHomotopy j').level n
        (s, (boundedFlatAffineSupportedSectionPrespectrumMap j j' f l h).map n x) := by
  have hn := prespectrumZeroTransformationHomotopy_naturality
    (boundedFlatAffineSupportedSectionForgetModelMap j ≫ boundedFlatAffineSectionOpenModelMap j)
    (boundedFlatAffineSupportedSectionForgetModelMap j' ≫ boundedFlatAffineSectionOpenModelMap j')
    (boundedFlatAffineSupportedSectionModelMap j j' f l h)
    (boundedFlatAffineSectionOpenReindexModelMap j j' f l h)
    (boundedFlatAffineSupportedSectionOpenModelSquare j j' f l h)
    (boundedFlatAffineSupportedSectionZeroToOpen j)
    (boundedFlatAffineSupportedSectionZeroToOpen j')
    (boundedFlatAffineSupportedSectionZeroToOpen_weak j)
    (boundedFlatAffineSupportedSectionZeroToOpen_weak j') n
  exact congrArg (fun H => H (unitInterval.symm s, x)) hn

end Quillen.PerfectComplexes
