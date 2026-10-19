/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedUnitQuotient
public import Quillen.KTheory.Bass.TwoChartDoubleDescent

/-!
# Two original supported forward-unit quotients

The original supported stable forward-unit quotient followed by its contracted
successor is represented by the two unchanged supported Laurent-track operations
and the two original cokernel projections. Its nonnegative components are
isomorphisms when the ambient scheme is qcqs and the removed open is compact.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry CommRingCat.PolynomialLaurent
open Quillen.Bass.TwoChart Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

/-- The two unchanged coefficient-supported stable Laurent operations before quotienting. -/
def boundedFlatCoefficientSupportedDoubleForwardUnitMap (a : Under R) (d : ℤ) :
    (stableHomotopyFunctor d).obj
        (prespectrum ((boundedFlatCoefficientSupportedModelFunctor f).obj a)) ⟶
      (stableHomotopyFunctor ((d + 1) + 1)).obj
        (prespectrum ((boundedFlatCoefficientSupportedModelFunctor f).obj
          ((laurentUnderFunctor R).obj ((laurentUnderFunctor R).obj a)))) :=
  ((boundedFlatCoefficientSupportedLaurentAction f).track.homotopy a).stableOperation d ≫
    ((boundedFlatCoefficientSupportedLaurentAction f).track.homotopy
      ((laurentUnderFunctor R).obj a)).stableOperation (d + 1)

/-- The original supported forward quotient followed by its contracted successor. -/
def boundedFlatCoefficientSupportedDoubleForwardUnitQuotient (d : ℤ) :=
  boundedFlatCoefficientSupportedForwardUnitQuotient f d ≫
    (contractionFunctor (underToLaurent R) (underToLaurentInvert R)).map
      (boundedFlatCoefficientSupportedForwardUnitQuotient f (d + 1))

/-- Both original quotient projections retain the two actual supported track operations. -/
theorem boundedFlatCoefficientSupportedDoubleForwardUnitQuotient_representative
    (a : Under R) (d : ℤ) :
    (boundedFlatCoefficientSupportedDoubleForwardUnitQuotient f d).app a =
      boundedFlatCoefficientSupportedDoubleForwardUnitMap f a d ≫
        doubleContractionπ (underToLaurent R) (underToLaurentInvert R)
          ((boundedFlatCoefficientSupportedModelFunctor f ⋙ prespectrumFunctor) ⋙
            stableHomotopyFunctor ((d + 1) + 1)) a := by
  simp only [boundedFlatCoefficientSupportedDoubleForwardUnitQuotient, NatTrans.comp_app,
    boundedFlatCoefficientSupportedForwardUnitQuotient,
    KTheory.Bass.LaurentSeed.Track.stableUnitQuotient,
    KTheory.Bass.LaurentSeed.Track.stableOperationNatTrans,
    boundedFlatCoefficientSupportedDoubleForwardUnitMap,
    contractionFunctor, doubleContractionπ, Category.assoc, contractionMap_π]

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- The two actual supported positive Bass isomorphisms remain invertible after composition. -/
instance boundedFlatCoefficientSupportedDoubleForwardUnitQuotient_isIso (n : ℕ) :
    IsIso (boundedFlatCoefficientSupportedDoubleForwardUnitQuotient f (n : ℤ)) := by
  have : IsIso (boundedFlatCoefficientSupportedForwardUnitQuotient f ((n : ℤ) + 1)) := by
    simpa only [Int.natCast_add, Int.natCast_one] using
      boundedFlatCoefficientSupportedForwardUnitQuotient_isIso f (n + 1)
  unfold boundedFlatCoefficientSupportedDoubleForwardUnitQuotient
  infer_instance

/-- The supported double comparison is invertible on every actual coefficient fiber. -/
instance boundedFlatCoefficientSupportedDoubleForwardUnitQuotient_app_isIso
    (a : Under R) (n : ℕ) :
    IsIso ((boundedFlatCoefficientSupportedDoubleForwardUnitQuotient f (n : ℤ)).app a) :=
  inferInstance

end Quillen.PerfectComplexes
