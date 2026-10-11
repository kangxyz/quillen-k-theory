/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassBottomComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassTelescope

/-!
# Original Bass negative classes in the actual telescope

Each original perfect-K-zero Bass class enters the actual telescope through its finite bottom
stage and the unchanged cylinder inclusion. The natural map does not assert stabilization.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- Original Bass negative classes enter through the actual stage-i cylinder inclusion. -/
def boundedFlatAffineSectionBassNegativeMap (i : ℕ) :
    Quillen.Bass.negativeKFunctor.{u} i ⟶
      boundedFlatAffineSectionBassTelescopeFunctor ⋙ stableHomotopyFunctor (-(i : ℤ)) :=
  (boundedFlatAffineSectionBassBottomComparison i).hom ≫
    Functor.whiskerRight (boundedFlatAffineSectionBassTelescopeInclusion i)
      (stableHomotopyFunctor (-(i : ℤ)))

/-- The component preserves the original finite-stage comparison and original telescope face. -/
theorem boundedFlatAffineSectionBassNegativeMap_app (i : ℕ) (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionBassNegativeMap i).app R =
      (boundedFlatAffineSectionBassBottomComparison i).hom.app R ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((boundedFlatAffineSectionBassTelescopeInclusion i).app R) := rfl

/-- The original Laurent quotient retains its actual finite-stage image in the telescope. -/
@[reassoc]
theorem boundedFlatAffineSectionBassNegativeMap_π (i : ℕ) (R : CommRingCat.{u}) :
    Quillen.Bass.negativeKπ R i ≫ (boundedFlatAffineSectionBassNegativeMap (i + 1)).app R =
    (boundedFlatAffineSectionBassBottomComparison i).hom.app
        (Quillen.Bass.laurentFunctor.obj R) ≫
      (Quillen.Bass.contractionπ (boundedFlatAffineSectionBassBottomFunctor i)).app R ≫
        (boundedFlatAffineSectionBassBottomContractionIso i).hom.app R ≫
          (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
            ((boundedFlatAffineSectionBassTelescopeInclusion (i + 1)).app R) := by
  rw [boundedFlatAffineSectionBassNegativeMap_app,
    boundedFlatAffineSectionBassBottomComparison_π_assoc]

end Quillen.PerfectComplexes
