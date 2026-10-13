/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassBottomCokernel
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassSuccessorStable
public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassNegativeGroups

/-!
# Original Bass negative groups at the bottom of each finite stage

The original perfect-K-zero Bass recursion is naturally the bottom signed stable group of each
actual finite strict Bass stage. The Laurent quotient is the original cone inclusion followed by
the genuine signed loop shift. This theorem does not assert stabilization of the seed maps.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes

/-- The actual bottom-degree contraction is the next original finite-stage bottom functor. -/
def boundedFlatAffineSectionBassBottomContractionIso (i : ℕ) :
    Quillen.Bass.contraction (boundedFlatAffineSectionBassBottomFunctor.{u} i) ≅
      boundedFlatAffineSectionBassBottomFunctor (i + 1) :=
  boundedFlatAffineSectionBassBottomConeNatIso i ≪≫
    (boundedFlatAffineSectionBassBottomSuccessorIso i).symm

/-- The already-defined original perfect-K-zero Bass groups are the actual finite-stage bottoms.
-/
def boundedFlatAffineSectionBassBottomComparison :
    (i : ℕ) → Quillen.Bass.negativeKFunctor.{u} i ≅
      boundedFlatAffineSectionBassBottomFunctor i
  | 0 => boundedFlatAffineSectionBassBottomZeroNatIso
  | i + 1 => Quillen.Bass.contractionFunctor.mapIso
      (boundedFlatAffineSectionBassBottomComparison i) ≪≫
        boundedFlatAffineSectionBassBottomContractionIso i

/-- The original Laurent quotient survives each actual finite-stage comparison. -/
@[reassoc]
theorem boundedFlatAffineSectionBassBottomComparison_π (i : ℕ) (R : CommRingCat.{u}) :
    Quillen.Bass.negativeKπ R i ≫
      (boundedFlatAffineSectionBassBottomComparison (i + 1)).hom.app R =
    (boundedFlatAffineSectionBassBottomComparison i).hom.app
        (Quillen.Bass.laurentFunctor.obj R) ≫
      (Quillen.Bass.contractionπ (boundedFlatAffineSectionBassBottomFunctor i)).app R ≫
        (boundedFlatAffineSectionBassBottomContractionIso i).hom.app R := by
  simp only [boundedFlatAffineSectionBassBottomComparison, Quillen.Bass.negativeKπ]
  exact Quillen.Bass.contractionMap_π_assoc _ _ _

end Quillen.PerfectComplexes
