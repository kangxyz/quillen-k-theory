/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedConnectiveInvertibility
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientTwoChartStableSequence
public import Quillen.KTheory.Bass.StrictLaurentInverseAction

/-!
# The original supported unit quotients and stage-zero chart exactness

For a qcqs ambient scheme and a compact removed open, the actual supported seed is invertible
in every nonnegative stable degree. Its exact original Laurent-track factorization and the
genuine spectral Bass short exact row therefore identify the original forward-unit quotient as
a natural isomorphism. The actual inverse unit gives its negative natural isomorphism. Original
stage-zero chart exactness follows from the same genuine row. No supported geometric first-
coordinate boundary or perfect scalar-operation evaluation comparison is asserted here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.LoopPrespectrum Quillen.KTheory.Bass Quillen.Bass.TwoChartStable
open CommRingCat.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- The actual inverse automorphism of the unchanged supported Laurent unit. -/
def boundedFlatCoefficientSupportedInverseLaurentAction :
    LaurentSeed.ModelAction (boundedFlatCoefficientSupportedModelFunctor f) :=
  (boundedFlatCoefficientSupportedLaurentAction f).symm

/-- The original supported forward unit followed by the original Laurent quotient. -/
def boundedFlatCoefficientSupportedForwardUnitQuotient (d : ℤ) :=
  (boundedFlatCoefficientSupportedLaurentAction f).track.stableUnitQuotient d

/-- The actual inverse supported unit followed by that same original quotient. -/
def boundedFlatCoefficientSupportedInverseUnitQuotient (d : ℤ) :=
  (boundedFlatCoefficientSupportedInverseLaurentAction f).track.stableUnitQuotient d

/-- The actual inverse-unit quotient is the negative original forward-unit quotient. -/
theorem boundedFlatCoefficientSupportedInverseUnitQuotient_eq_neg (d : ℤ) :
    boundedFlatCoefficientSupportedInverseUnitQuotient f d =
      -boundedFlatCoefficientSupportedForwardUnitQuotient f d :=
  (boundedFlatCoefficientSupportedLaurentAction f).symm_stableUnitQuotient d

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- The actual stage-zero forward unit quotient is invertible on every coefficient object. -/
instance boundedFlatCoefficientSupportedForwardUnitQuotient_app_isIso (a : Under R) (n : ℕ) :
    IsIso ((boundedFlatCoefficientSupportedForwardUnitQuotient f (n : ℤ)).app a) := by
  let A := (boundedFlatCoefficientSupportedLaurentAction f).track
  let : IsIso ((stableHomotopyFunctor (n : ℤ)).map (A.seedMap a)) := by
    change IsIso ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedFlatCoefficientSupportedBassTransition f 0).app a))
    infer_instance
  exact A.stableUnitQuotient_isIso_of_seed a
    (boundedFlatCoefficientSupportedTwoChartSpectralConditions f 0 a) (n : ℤ)

/-- The original supported forward-unit quotient is a natural isomorphism. -/
instance boundedFlatCoefficientSupportedForwardUnitQuotient_isIso (n : ℕ) :
    IsIso (boundedFlatCoefficientSupportedForwardUnitQuotient f (n : ℤ)) :=
  NatIso.isIso_of_isIso_app _

/-- The original inverse supported unit quotient is a natural isomorphism. -/
instance boundedFlatCoefficientSupportedInverseUnitQuotient_isIso (n : ℕ) :
    IsIso (boundedFlatCoefficientSupportedInverseUnitQuotient f (n : ℤ)) := by
  let : IsIso ((boundedFlatCoefficientSupportedLaurentAction f).track.stableUnitQuotient
      (n : ℤ)) := boundedFlatCoefficientSupportedForwardUnitQuotient_isIso f n
  exact (boundedFlatCoefficientSupportedLaurentAction f).symm_stableUnitQuotient_isIso (n : ℤ)

/-- The unchanged supported chart complex is exact in every nonnegative degree, including zero.
-/
theorem boundedFlatCoefficientSupportedStageZeroChart_exact (a : Under R) (n : ℕ) :
    (chartComplex ((boundedFlatCoefficientSupportedBassDiagram f 0).mapArrow.mapArrow.obj
      (laurentUnderSquare R a)) (n : ℤ)).Exact := by
  let A := (boundedFlatCoefficientSupportedLaurentAction f).track
  let : IsIso ((stableHomotopyFunctor (n : ℤ)).map (A.seedMap a)) := by
    change IsIso ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedFlatCoefficientSupportedBassTransition f 0).app a))
    infer_instance
  exact (ShortComplex.ab_exact_iff_function_exact _).mpr
    (A.chart_exact_of_seed a
      (boundedFlatCoefficientSupportedTwoChartSpectralConditions f 0 a) (n : ℤ))

end Quillen.PerfectComplexes
