/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassNegativeMap

/-! Original coefficients and Laurent representatives for the actual negative-class map. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum Quillen.PerfectComplexes
universe u
namespace Quillen.Tests.SectionBassNegativeMap

/-- The map lands in the unchanged telescope with its literal coefficient action. -/
theorem original_coefficient (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S) :
    Quillen.Bass.negativeKMap f i ≫ (boundedFlatAffineSectionBassNegativeMap i).app S =
      (boundedFlatAffineSectionBassNegativeMap i).app R ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          (boundedFlatAffineSectionBassTelescopeMap f) :=
  (boundedFlatAffineSectionBassNegativeMap i).naturality f

/-- Every original negative class enters through its actual finite-stage cylinder face. -/
theorem original_stage_face (i : ℕ) (R : CommRingCat.{u})
    (x : Quillen.Bass.negativeK R i) :
    (boundedFlatAffineSectionBassNegativeMap i).app R x =
      ((boundedFlatAffineSectionBassBottomComparison i).hom.app R ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((boundedFlatAffineSectionBassTelescopeInclusion i).app R)) x := rfl

/-- The original Laurent quotient formula remains valid after entering the actual telescope. -/
theorem original_laurent_projection (i : ℕ) (R : CommRingCat.{u})
    (x : Quillen.Bass.negativeK (Quillen.Bass.laurentFunctor.obj R) i) :
    (Quillen.Bass.negativeKπ R i ≫ (boundedFlatAffineSectionBassNegativeMap (i + 1)).app R) x =
    ((boundedFlatAffineSectionBassBottomComparison i).hom.app
        (Quillen.Bass.laurentFunctor.obj R) ≫
      (Quillen.Bass.contractionπ (boundedFlatAffineSectionBassBottomFunctor i)).app R ≫
        (boundedFlatAffineSectionBassBottomContractionIso i).hom.app R ≫
          (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
            ((boundedFlatAffineSectionBassTelescopeInclusion (i + 1)).app R)) x :=
  ConcreteCategory.congr_hom (boundedFlatAffineSectionBassNegativeMap_π i R) x

/-- The next original stage inclusion gives the same image after the actual seed transition. -/
theorem original_next_stage (i : ℕ) (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionBassNegativeMap i).app R =
      (boundedFlatAffineSectionBassBottomComparison i).hom.app R ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((boundedFlatAffineSectionBassTransition i).app R) ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((boundedFlatAffineSectionBassTelescopeInclusion (i + 1)).app R) := by
  rw [boundedFlatAffineSectionBassNegativeMap_app,
    (boundedFlatAffineSectionBassTelescopeInclusionHomotopy R i).stableHomotopyMap_eq
      (-(i : ℤ)), Functor.map_comp]

end Quillen.Tests.SectionBassNegativeMap
