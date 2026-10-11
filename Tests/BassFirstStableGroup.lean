/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassFirstStableGroup

/-!
Original perfect-complex Laurent representatives, literal chart signs, arbitrary first-step
classes and the actual strict/raw evaluation map are retained by the degree-minus-one comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.PerfectComplexes
universe u
namespace Quillen.Tests.BassFirstStableGroup

/-- Every actual original raw first-step class has an original Laurent K-zero representative. -/
theorem original_representative (R : CommRingCat.{u})
    (z : stableHomotopyGroup (boundedFlatAffineBassStep R) (-1)) :
    ∃ x : Quillen.Bass.affineKZeroFunctor.obj (.of (LaurentPolynomial R)),
      boundedFlatBassFirstLaurentMap R x = z :=
  boundedFlatBassFirstLaurentMap_surjective R z

/-- The relation is precisely the original positive chart minus the original inverse chart. -/
theorem original_relation (R : CommRingCat.{u})
    (x : Quillen.Bass.negativeK (Quillen.Bass.laurentFunctor.obj R) 0) :
    boundedFlatBassFirstLaurentMap R x = 0 ↔
      ∃ a b : Quillen.Bass.negativeK (Quillen.Bass.polynomialFunctor.obj R) 0,
        Quillen.Bass.negativeKMap (Quillen.Bass.plus.app R) 0 a -
          Quillen.Bass.negativeKMap (Quillen.Bass.minus.app R) 0 b = x :=
  boundedFlatBassFirstLaurentMap_eq_zero_iff R x

/-- Every original perfect K-zero Laurent class retains its original quotient image. -/
theorem original_laurent_class (R : CommRingCat.{u})
    (a : Quillen.Bass.negativeK (Quillen.Bass.laurentFunctor.obj R) 0) :
    (boundedFlatBassFirstStableGroupIso R).hom (Quillen.Bass.negativeKπ R 0 a) =
      boundedFlatBassFirstLaurentMap R a :=
  ConcreteCategory.congr_hom (boundedFlatBassFirstStableGroupIso_π R) a

/-- The actual one-step evaluation carries the strict-stage class to the original raw class. -/
theorem original_evaluation (R : CommRingCat.{u}) (a : Quillen.Bass.negativeK R 1) :
    (stableHomotopyFunctor (-1)).map (boundedFlatAffineSectionBassStepEvaluation R)
      ((boundedFlatAffineSectionBassFirstStableGroupIso R).hom a) =
    (boundedFlatBassFirstStableGroupIso R).hom a :=
  ConcreteCategory.congr_hom (boundedFlatAffineSectionBassFirstStableGroupIso_evaluation R) a

/-- Every genuine strict first-stage class is recovered by the actual inverse comparison. -/
theorem original_strict_round_trip (R : CommRingCat.{u})
    (z : stableHomotopyGroup ((boundedFlatAffineSectionBassDiagram 1).obj R) (-1)) :
    (boundedFlatAffineSectionBassFirstStableGroupIso R).hom
      ((boundedFlatAffineSectionBassFirstStableGroupIso R).inv z) = z :=
  ConcreteCategory.congr_hom (boundedFlatAffineSectionBassFirstStableGroupIso R).inv_hom_id z

/-- The explicit chart-sign change negates only the second original inclusion. -/
theorem second_chart_sign (R : CommRingCat.{u}) :
    (biprod.inr : Quillen.Bass.affineKZeroFunctor.obj (.of (Polynomial R)) ⟶
      Quillen.Bass.affineKZeroFunctor.obj (.of (Polynomial R)) ⊞
        Quillen.Bass.affineKZeroFunctor.obj (.of (Polynomial R))) ≫
      (Quillen.Bass.secondChartNegation _ _).hom = -biprod.inr := by
  simp [Quillen.Bass.secondChartNegation]

end Quillen.Tests.BassFirstStableGroup
