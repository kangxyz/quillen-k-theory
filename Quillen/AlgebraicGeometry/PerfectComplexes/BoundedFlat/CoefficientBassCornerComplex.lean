/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSplitMaps

/-!
# The original coefficient Bass difference on the split corner quotient

The common corner and both original Laurent charts assemble as a short complex of actual
coefficient functors. Its original difference descends through the naturally split corner
cokernel. The resulting map retains the literal representative equation, without geometric
hypotheses or a replacement of the original quotient.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CommRingCat.PolynomialLaurent Quillen.Bass.TwoChart
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The original two-chart difference as a natural transformation of coefficient functors. -/
def boundedFlatCoefficientDifference (n : ℕ) :
    boundedFlatCoefficientPolynomialPairFunctor P n ⟶
      laurentUnderFunctor R ⋙ boundedFlatCoefficientKAddFunctor P n where
  app a := polynomialDifference (underToLaurent R) (underToLaurentInvert R)
    (boundedFlatCoefficientKAddFunctor P n) a
  naturality {_a _b} f := polynomialDifference_naturality _ _ _ f

/-- Both original charts agree on the actual common corner. -/
@[reassoc (attr := simp)]
theorem boundedFlatCoefficientCorner_difference (n : ℕ) :
    boundedFlatCoefficientCorner P n ≫ boundedFlatCoefficientDifference P n = 0 := by
  apply NatTrans.ext
  funext a
  let F := boundedFlatCoefficientKAddFunctor P n
  change biprod.lift (F.map ((polynomialUnderCoefficient R).app a))
      (F.map ((polynomialUnderCoefficient R).app a)) ≫
        biprod.desc (F.map ((underToLaurent R).app a))
          (-F.map ((underToLaurentInvert R).app a)) =
    (0 : F.obj a ⟶ F.obj ((laurentUnderFunctor R).obj a))
  rw [biprod.lift_desc, Preadditive.comp_neg, ← Functor.map_comp, ← Functor.map_comp,
    polynomialUnderCoefficient_toLaurent, polynomialUnderCoefficient_toLaurentInvert,
    add_neg_cancel]

/-- The original common-corner and chart-difference maps form the actual Bass middle row. -/
def boundedFlatCoefficientMiddleSequence (n : ℕ) :
    ShortComplex (Under R ⥤ AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk (boundedFlatCoefficientCorner P n) (boundedFlatCoefficientDifference P n)
    (boundedFlatCoefficientCorner_difference P n)

/-- The unchanged two-chart difference descends through the original corner cokernel. -/
def boundedFlatCoefficientDifferenceDesc (n : ℕ) :
    cokernel (boundedFlatCoefficientCorner P n) ⟶
      laurentUnderFunctor R ⋙ boundedFlatCoefficientKAddFunctor P n :=
  cokernel.desc _ (boundedFlatCoefficientDifference P n)
    (boundedFlatCoefficientCorner_difference P n)

/-- The descended difference retains its original natural representative equation. -/
@[reassoc (attr := simp)]
theorem boundedFlatCoefficientDifferenceDesc_π (n : ℕ) :
    cokernel.π (boundedFlatCoefficientCorner P n) ≫
      boundedFlatCoefficientDifferenceDesc P n = boundedFlatCoefficientDifference P n :=
  cokernel.π_desc _ _ _

/-- The actual inverse unit followed by the original Laurent quotient, naturally in coefficients. -/
def boundedFlatCoefficientInverseUnitQuotient (n : ℕ) :
    boundedFlatCoefficientKAddFunctor P n ⟶
      contraction (underToLaurent R) (underToLaurentInvert R)
        (boundedFlatCoefficientKAddFunctor P (n + 1)) :=
  boundedFlatCoefficientInverseUnitSection P n ≫
    contractionπ (underToLaurent R) (underToLaurentInvert R)
      (boundedFlatCoefficientKAddFunctor P (n + 1))

/-- Each component retains exactly the original inverse unit and original quotient projection. -/
@[simp]
theorem boundedFlatCoefficientInverseUnitQuotient_app (n : ℕ) (a : Under R) :
    (boundedFlatCoefficientInverseUnitQuotient P n).app a =
      (boundedFlatCoefficientInverseUnitSection P n).app a ≫
        (contractionπ (underToLaurent R) (underToLaurentInvert R)
          (boundedFlatCoefficientKAddFunctor P (n + 1))).app a := rfl

end Quillen.PerfectComplexes
