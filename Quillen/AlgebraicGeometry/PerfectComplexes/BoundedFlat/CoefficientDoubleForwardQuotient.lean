/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassForwardQuotient
public import Quillen.KTheory.Bass.TwoChartDoubleDescent

/-!
# The actual twice-positive coefficient Bass representative

The composite of the original forward-unit quotient with its once-contracted
successor is represented by the two original Laurent-unit operations followed
by the two original quotient projections. For a fixed quasi-compact,
quasi-separated base this composite is an isomorphism. No action of a variable
swap on the double quotient is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry CommRingCat.PolynomialLaurent
open Quillen.Bass.TwoChart
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The two actual forward Laurent operations before either Bass quotient. -/
def boundedFlatCoefficientDoubleForwardUnitMap (a : Under R) (n : ℕ) :
    (boundedFlatCoefficientKAddFunctor P n).obj a ⟶
      (boundedFlatCoefficientKAddFunctor P (n + 2)).obj
        ((laurentUnderFunctor R).obj ((laurentUnderFunctor R).obj a)) :=
  (boundedFlatCoefficientForwardUnitSection P n).app a ≫
    (boundedFlatCoefficientForwardUnitSection P (n + 1)).app ((laurentUnderFunctor R).obj a)

/-- The original positive Bass comparison followed by its genuinely contracted successor. -/
def boundedFlatCoefficientDoubleForwardUnitQuotient (n : ℕ) :
    boundedFlatCoefficientKAddFunctor P n ⟶
      contraction (underToLaurent R) (underToLaurentInvert R)
        (contraction (underToLaurent R) (underToLaurentInvert R)
          (boundedFlatCoefficientKAddFunctor P (n + 2))) :=
  boundedFlatCoefficientForwardUnitQuotient P n ≫
    (contractionFunctor (underToLaurent R) (underToLaurentInvert R)).map
      (boundedFlatCoefficientForwardUnitQuotient P (n + 1))

/-- Both original quotient projections retain precisely the two forward-unit representatives. -/
theorem boundedFlatCoefficientDoubleForwardUnitQuotient_representative (a : Under R) (n : ℕ) :
    (boundedFlatCoefficientDoubleForwardUnitQuotient P n).app a =
      boundedFlatCoefficientDoubleForwardUnitMap P a n ≫
        doubleContractionπ (underToLaurent R) (underToLaurentInvert R)
          (boundedFlatCoefficientKAddFunctor P (n + 2)) a := by
  simp only [boundedFlatCoefficientDoubleForwardUnitQuotient, NatTrans.comp_app,
    boundedFlatCoefficientForwardUnitQuotient, boundedFlatCoefficientDoubleForwardUnitMap,
    contractionFunctor, doubleContractionπ, Category.assoc, contractionMap_π]

variable [CompactSpace P.left] [QuasiSeparatedSpace P.left]

set_option backward.isDefEq.respectTransparency.types false in
/-- Both actual positive Bass isomorphisms remain invertible after their fixed composition. -/
instance boundedFlatCoefficientDoubleForwardUnitQuotient_isIso (n : ℕ) :
    IsIso (boundedFlatCoefficientDoubleForwardUnitQuotient P n) := by
  unfold boundedFlatCoefficientDoubleForwardUnitQuotient
  infer_instance

/-- The original double representative is an isomorphism at every coefficient object. -/
instance boundedFlatCoefficientDoubleForwardUnitQuotient_app_isIso (a : Under R) (n : ℕ) :
    IsIso ((boundedFlatCoefficientDoubleForwardUnitQuotient P n).app a) := inferInstance

end Quillen.PerfectComplexes
