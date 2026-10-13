/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassSeed

/-!
# Iterating the original strict geometric Bass seed

All connecting arrows are the existing Bass endofunctor's iterated images of the single proved
original Laurent seed. Every stage retains all coefficient maps, with strict naturality. No
new unit or independently supplied transition is chosen at any later iterate.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- Every connecting arrow is the actual nth Bass image of the same original geometric seed. -/
def boundedFlatAffineSectionBassTransition (n : ℕ) :
    boundedFlatAffineSectionBassDiagram.{u} n ⟶ boundedFlatAffineSectionBassDiagram (n + 1) :=
  KTheory.Bass.strictRingDiagramTransition boundedFlatAffineSectionBassSeed n

/-- The initial connecting arrow is the unchanged proved original seed. -/
theorem boundedFlatAffineSectionBassTransition_zero :
    boundedFlatAffineSectionBassTransition.{u} 0 = boundedFlatAffineSectionBassSeed := rfl

/-- Every original coefficient map commutes literally with every actual iterated transition. -/
theorem boundedFlatAffineSectionBassTransition_naturality (n : ℕ)
    {R S : CommRingCat.{u}} (f : R ⟶ S) :
    (boundedFlatAffineSectionBassDiagram n).map f ≫
        (boundedFlatAffineSectionBassTransition n).app S =
      (boundedFlatAffineSectionBassTransition n).app R ≫
        (boundedFlatAffineSectionBassDiagram (n + 1)).map f :=
  (boundedFlatAffineSectionBassTransition n).naturality f

/-- At every level the iterated transition retains the same strict coefficient square. -/
theorem boundedFlatAffineSectionBassTransition_naturality_apply (n k : ℕ)
    {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : ((boundedFlatAffineSectionBassDiagram n).obj R).space k) :
    ((boundedFlatAffineSectionBassTransition n).app S).map k
        (((boundedFlatAffineSectionBassDiagram n).map f).map k x) =
      ((boundedFlatAffineSectionBassDiagram (n + 1)).map f).map k
        (((boundedFlatAffineSectionBassTransition n).app R).map k x) :=
  congrArg (fun a ↦ a.map k x) (boundedFlatAffineSectionBassTransition_naturality n f)

end Quillen.PerfectComplexes
