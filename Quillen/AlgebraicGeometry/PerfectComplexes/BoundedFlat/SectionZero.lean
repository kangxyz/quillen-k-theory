/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SectionEquivalence
public import Quillen.CategoryTheory.FiberedCategory.GrothendieckZeroSections

/-!
# The original chosen zeros form a strictly reindexed bounded-flat section

The pointwise section uses the already chosen zero of the actual bounded-flat Waldhausen
category at each target ring. Original exact pullbacks give its strong cocartesianness.
Both coefficient reindexing and original evaluation retain these chosen zeros literally.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.CategoryTheory.GrothendieckZeroSections
universe u
namespace Quillen.PerfectComplexes

/-- The original chosen zero family, independent of any source ring. -/
def boundedFlatAffineChosenZero (S : CommRingCat.{u}) :
    boundedFlatAffinePseudofunctor.obj ⟨S⟩ :=
  (boundedFlatPerfectWaldhausen (Spec S)).zero

/-- The existing chosen objects retain their actual zero universal properties. -/
theorem boundedFlatAffineChosenZero_isZero (S : CommRingCat.{u}) :
    IsZero (boundedFlatAffineChosenZero S) := (boundedFlatPerfectWaldhausen (Spec S)).isZero

/-- Actual exact pullback preserves the chosen zero's universal property. -/
theorem boundedFlatAffineChosenZero_map_isZero {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsZero ((boundedFlatAffinePseudofunctor.map f.toLoc).toFunctor.obj
      (boundedFlatAffineChosenZero R)) :=
  (boundedFlatPerfectPullback (Spec.map f)).map_isZero
    (boundedFlatPerfectWaldhausen (Spec R)).isZero

/-- The chosen zero section uses the original bounded-flat zeros in every fiber. -/
def boundedFlatAffineSectionZero (R : CommRingCat.{u}) : BoundedFlatAffineSections R :=
  sectionZero boundedFlatAffinePseudofunctor boundedFlatAffineChosenZero
    boundedFlatAffineChosenZero_isZero (fun {_ _} f => boundedFlatAffineChosenZero_map_isZero f) R

/-- The specified pointwise zero section really is a zero object. -/
theorem isZero_boundedFlatAffineSectionZero (R : CommRingCat.{u}) :
    IsZero (boundedFlatAffineSectionZero R) :=
  isZero_sectionZero boundedFlatAffinePseudofunctor boundedFlatAffineChosenZero
    boundedFlatAffineChosenZero_isZero (fun {_ _} f => boundedFlatAffineChosenZero_map_isZero f) R

/-- Original evaluation retains the existing Waldhausen zero literally. -/
theorem boundedFlatAffineOriginalEvaluation_sectionZero (R : CommRingCat.{u}) :
    (boundedFlatAffineOriginalEvaluation R).obj (boundedFlatAffineSectionZero R) =
      (boundedFlatPerfectWaldhausen (Spec R)).zero :=
  originalEvaluation_sectionZero boundedFlatAffinePseudofunctor boundedFlatAffineChosenZero
    boundedFlatAffineChosenZero_isZero (fun {_ _} f => boundedFlatAffineChosenZero_map_isZero f) R

/-- Strict coefficient restriction retains the chosen zero section literally. -/
theorem boundedFlatAffineSectionsMap_sectionZero {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedFlatAffineSectionsMap f).obj (boundedFlatAffineSectionZero R) =
      boundedFlatAffineSectionZero S :=
  reindex_sectionZero boundedFlatAffinePseudofunctor boundedFlatAffineChosenZero
    boundedFlatAffineChosenZero_isZero (fun {_ _} f => boundedFlatAffineChosenZero_map_isZero f) f

end Quillen.PerfectComplexes
