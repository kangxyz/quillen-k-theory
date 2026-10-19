/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterNegativeSign
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAmbientDoubleSign

/-!
# Identity of every original ambient negative-class correction

The actual parameter Model quotient sign on affine coefficient spectra feeds
the proved finite-word calculation in every index. This removes the finite
correction from the original current-to-fine class comparison without changing
its class maps, Laurent units, or finite-bottom isomorphisms.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace Quillen.PerfectComplexes.GlobalParameterCoefficient
open GlobalSectionChangeIndex SchemeNaturalSeed
variable (P : Over (Spec (CommRingCat.of (ULift.{u} ℤ))))
  [CompactSpace P.left] [QuasiSeparatedSpace P.left]

/-- Every original ambient negative correction is identity. -/
theorem negativeClassCorrection_hom (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (negativeClassCorrection P i a).hom = 𝟙 _ := by
  apply negativeClassCorrection_hom_of_spec_swap P _ i a
  intro b
  have : QuasiSeparatedSpace (coefficientParameterScheme b).unop.obj :=
    inferInstanceAs (QuasiSeparatedSpace (Spec b.right))
  exact parameter_doubleContractionSwap_neg P (coefficientParameterScheme b)

/-- The specified current-to-fine comparison preserves all original ambient negative classes. -/
@[reassoc]
theorem currentNegativeKComparison_fine (i : ℕ)
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (currentNegativeKComparison P i).hom.app a ≫
        (currentIteratedStableIso (ParameterModels.ambient P.left)
          (ParameterLaurentTrack.ambientTrack P.left) (specUnder.obj a) (-(i : ℤ))).hom ≫
        (stableHomotopyFunctor (-(i : ℤ))).map ((fineTelescopeComparison P).app a) =
      (boundedFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom.app a := by
  rw [currentNegativeKComparison_fine_correction, negativeClassCorrection_hom, Category.id_comp]

end Quillen.PerfectComplexes.GlobalParameterCoefficient
