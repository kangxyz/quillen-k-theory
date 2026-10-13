/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassDiagram

/-!
# Consumers of the actual all-stage section Bass diagrams

These are genuine iterated objects and coefficient actions. No connecting seed is supplied.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
universe u
namespace QuillenTest.SectionBassDiagram

open Quillen

/-- Stage zero retains the actual original section spectrum map. -/
theorem original_stage_zero {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedFlatAffineSectionBassDiagram 0).map f =
      boundedFlatAffineSectionPrespectrumFunctor.map f := rfl

/-- Every actual iterated stage retains literal coefficient identity. -/
theorem all_stage_identity (n : ℕ) (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionBassDiagram n).map (𝟙 R) =
      𝟙 ((boundedFlatAffineSectionBassDiagram n).obj R) :=
  (boundedFlatAffineSectionBassDiagram n).map_id R

/-- Every actual iterated stage retains literal composition of independent coefficient maps. -/
theorem all_stage_composition (n : ℕ) {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    (boundedFlatAffineSectionBassDiagram n).map (f ≫ g) =
      (boundedFlatAffineSectionBassDiagram n).map f ≫
        (boundedFlatAffineSectionBassDiagram n).map g :=
  (boundedFlatAffineSectionBassDiagram n).map_comp f g

end QuillenTest.SectionBassDiagram
