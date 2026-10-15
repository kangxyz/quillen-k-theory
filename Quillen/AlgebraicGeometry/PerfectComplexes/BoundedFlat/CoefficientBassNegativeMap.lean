/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassOriginalNegativeComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedBassTelescope

/-!
# Original scheme Bass classes in the native coefficient telescope

For a compact ambient scheme, each original negative class enters the actual
native telescope through its finite bottom comparison and unchanged stage
inclusion. Coefficient arrows and the original Laurent quotient are preserved.
No injectivity, surjectivity, seed stabilization or classical TT identification
is asserted.
-/

@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]

/-- Original scheme negative classes enter through the original stage-i inclusion. -/
def boundedFlatCoefficientAmbientBassNegativeMap (i : ℕ) :
    boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor i ⟶
      boundedFlatCoefficientAmbientBassTelescopeFunctor P ⋙
        stableHomotopyFunctor (-(i : ℤ)) :=
  (boundedFlatCoefficientAmbientNegativeKComparison P i).hom ≫
    Functor.whiskerRight (boundedFlatCoefficientAmbientBassTelescopeInclusion P i)
      (stableHomotopyFunctor (-(i : ℤ)))

/-- The component uses the unchanged finite comparison and cylinder inclusion. -/
theorem boundedFlatCoefficientAmbientBassNegativeMap_app (i : ℕ) (a : Under R) :
    (boundedFlatCoefficientAmbientBassNegativeMap P i).app a =
      (boundedFlatCoefficientAmbientNegativeKComparison P i).hom.app a ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((boundedFlatCoefficientAmbientBassTelescopeInclusion P i).app a) := rfl

/-- Every original Laurent representative has its specified successor-stage telescope image. -/
@[reassoc]
theorem boundedFlatCoefficientAmbientBassNegativeMap_π (i : ℕ) (a : Under R) :
    (Bass.negativeKFunctor i).map ((boundedFlatCoefficientLaurentIso P).hom.app a) ≫
      Bass.negativeKπ ((boundedFlatCoefficientQuasiCompactRow P).obj a).unop i ≫
        (boundedFlatCoefficientAmbientBassNegativeMap P (i + 1)).app a =
    (boundedFlatCoefficientAmbientNegativeKComparison P i).hom.app
        ((laurentUnderFunctor R).obj a) ≫
      (Quillen.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
        (boundedFlatCoefficientAmbientBassDiagram P i ⋙
          stableHomotopyFunctor (-(i : ℤ)))).app a ≫
        (boundedFlatCoefficientAmbientBassBottomContractionIso P i).hom.app a ≫
          (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
            ((boundedFlatCoefficientAmbientBassTelescopeInclusion P (i + 1)).app a) := by
  rw [boundedFlatCoefficientAmbientBassNegativeMap_app,
    boundedFlatCoefficientAmbientNegativeKComparison_π_assoc]

end Quillen.PerfectComplexes
