/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNegativeSign
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedParameterDoubleCorrection

/-!
# Identity of every original supported negative-class correction

The genuine supported two-unit sign and the actual positive coefficient
comparisons supply the original parameter quotient sign on every integral
Spec fiber. The affine-family finite-word theorem then fixes every original
supported negative class, retaining the original finite-bottom comparisons.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace Quillen.PerfectComplexes.GlobalSupportedParameterCoefficient
open GlobalSectionChangeIndex SchemeNaturalSeed
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- Every unchanged original supported negative correction is identity. -/
theorem negativeClassCorrection_hom (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (negativeClassCorrection f i a).hom = 𝟙 _ :=
  negativeClassCorrection_hom_of_spec_swap f
    (SupportedParameterCoefficientUnitOperation.parameterDiagram_quotient_swap f) i a

/-- The specified current-to-fine comparison preserves every original supported negative class. -/
@[reassoc]
theorem currentNegativeKComparison_fine (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (currentNegativeKComparison f i).hom.app a ≫
        (currentIteratedStableIso (ParameterModels.supported f.left)
          (ParameterLaurentTrack.supportedTrack f.left) (specUnder.obj a) (-(i : ℤ))).hom ≫
        (stableHomotopyFunctor (-(i : ℤ))).map ((fineTelescopeComparison f).app a) =
      (boundedFlatCoefficientSupportedNegativeKTelescopeComparison f i).hom.app a := by
  rw [currentNegativeKComparison_fine_correction, negativeClassCorrection_hom, Category.id_comp]

end Quillen.PerfectComplexes.GlobalSupportedParameterCoefficient
