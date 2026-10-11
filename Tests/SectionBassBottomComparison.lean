/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassBottomComparison

/-! Consumers of the original finite-stage bottom groups, coefficient maps and Laurent quotient. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Quillen.LoopPrespectrum Quillen.PerfectComplexes
universe u
namespace Quillen.Tests.SectionBassBottomComparison

/-- Every original Bass class is compared naturally along the actual strict coefficient map. -/
theorem original_coefficient (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S)
    (x : Quillen.Bass.negativeK R i) :
    (Quillen.Bass.negativeKMap f i ≫
      (boundedFlatAffineSectionBassBottomComparison i).hom.app S) x =
    ((boundedFlatAffineSectionBassBottomComparison i).hom.app R ≫
      (stableHomotopyFunctor (-(i : ℤ))).map
        ((boundedFlatAffineSectionBassDiagram i).map f)) x :=
  ConcreteCategory.congr_hom
    ((boundedFlatAffineSectionBassBottomComparison i).hom.naturality f) x

/-- The inverse comparison is defined on every genuine original stage-bottom class. -/
theorem original_roundtrip (i : ℕ) (R : CommRingCat.{u})
    (x : (boundedFlatAffineSectionBassBottomFunctor i).obj R) :
    (boundedFlatAffineSectionBassBottomComparison i).hom.app R
      ((boundedFlatAffineSectionBassBottomComparison i).inv.app R x) = x := by
  exact ConcreteCategory.congr_hom
    ((boundedFlatAffineSectionBassBottomComparison i).app R).inv_hom_id x

/-- The original recursive quotient represents each next-stage class by its original Laurent class.
-/
theorem original_laurent_projection (i : ℕ) (R : CommRingCat.{u})
    (x : Quillen.Bass.negativeK (Quillen.Bass.laurentFunctor.obj R) i) :
    (Quillen.Bass.negativeKπ R i ≫
      (boundedFlatAffineSectionBassBottomComparison (i + 1)).hom.app R) x =
    ((boundedFlatAffineSectionBassBottomComparison i).hom.app
        (Quillen.Bass.laurentFunctor.obj R) ≫
      (Quillen.Bass.contractionπ (boundedFlatAffineSectionBassBottomFunctor i)).app R ≫
        (boundedFlatAffineSectionBassBottomContractionIso i).hom.app R) x :=
  ConcreteCategory.congr_hom (boundedFlatAffineSectionBassBottomComparison_π i R) x

/-- Both chart signs are retained in the relation killed by the original cone inclusion. -/
theorem original_chart_difference (i : ℕ) (R : CommRingCat.{u}) :
    Quillen.Bass.polynomialDifference (boundedFlatAffineSectionBassBottomFunctor i) R ≫
      (stableHomotopyFunctor (-(i : ℤ))).map (mappingConeInclusion
        (StrictSquare.comparison
          ((boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj
            (Quillen.PolynomialBaseChange.laurentSquare R)))) = 0 := by
  rw [← boundedFlatAffineSectionBassBottomConeIso_π, ← Category.assoc]
  simp only [Quillen.Bass.polynomialDifference_contractionπ, Limits.zero_comp]

/-- The original perfect-K-zero comparison retains evaluation at stage zero. -/
theorem original_zero_evaluation (R : CommRingCat.{u}) :
    (boundedFlatAffineSectionBassBottomComparison 0).hom.app R ≫
      (stableHomotopyFunctor 0).map (boundedFlatAffineSectionEvaluationPrespectrumMap R) =
    (boundedFlatAffineStableKZeroIso R).hom :=
  boundedFlatAffineSectionBassBottomZeroIso_evaluation R

end Quillen.Tests.SectionBassBottomComparison
