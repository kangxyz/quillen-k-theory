/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedUnitQuotient
public import Quillen.KTheory.Bass.TwoChartSplitExact
public import Quillen.Aglib.Algebra.Polynomial.Laurent.UnderZero

/-!
# Two naturally split rows for the original supported coefficient spectrum

Actual polynomial zero evaluation splits the original common corner. The genuine inverse
Laurent Model action and its original quotient isomorphism define the canonical boundary and
split the second row. Consequently every additive endofunctor of coefficient group diagrams
preserves the original positive middle row. The ambient scheme is qcqs and the removed open
is compact. The canonical boundary is not identified here with a geometric projective-line
first-coordinate boundary or a transported perfect scalar operation.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.LoopPrespectrum Quillen.Bass.TwoChart
open CommRingCat.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left]

/-- Both original Laurent charts have the same actual common coefficient map. -/
theorem boundedFlatCoefficientSupportedCommonCorner :
    polynomialUnderCoefficient R ≫ underToLaurent R =
      polynomialUnderCoefficient R ≫ underToLaurentInvert R := by
  apply NatTrans.ext
  funext a
  exact (polynomialUnderCoefficient_toLaurent R a).trans
    (polynomialUnderCoefficient_toLaurentInvert R a).symm

/-- The unchanged stable groups of the original supported section Model. -/
def boundedFlatCoefficientSupportedStableGroupFunctor (d : ℤ) :
    Under R ⥤ AddCommGrpCat.{u + 1} :=
  boundedFlatCoefficientSupportedPrespectrumFunctor f ⋙ stableHomotopyFunctor d

/-- The original supported corner and signed Laurent chart difference. -/
def boundedFlatCoefficientSupportedMiddleSequence (d : ℤ) :
    ShortComplex (Under R ⥤ AddCommGrpCat.{u + 1}) :=
  middleComplex (polynomialUnderCoefficient R) (underToLaurent R) (underToLaurentInvert R)
    (boundedFlatCoefficientSupportedCommonCorner (R := R))
    (boundedFlatCoefficientSupportedStableGroupFunctor f d)

/-- Actual zero evaluation naturally splits the original supported corner quotient row. -/
def boundedFlatCoefficientSupportedCornerSplitting (d : ℤ) :
    (ShortComplex.cokernelSequence
      (boundedFlatCoefficientSupportedMiddleSequence f d).f).Splitting :=
  middleCornerSplitting (polynomialUnderCoefficient R) (underToLaurent R)
    (underToLaurentInvert R) (polynomialUnderZeroNat R) (polynomialUnderCoefficient_zeroNat R)
      (boundedFlatCoefficientSupportedStableGroupFunctor f d)

/-- The actual inverse supported Laurent unit as a natural degree-raising section. -/
def boundedFlatCoefficientSupportedInverseUnitSection (d : ℤ) :
    boundedFlatCoefficientSupportedStableGroupFunctor f d ⟶
      laurentUnderFunctor R ⋙ boundedFlatCoefficientSupportedStableGroupFunctor f (d + 1) :=
  (boundedFlatCoefficientSupportedInverseLaurentAction f).track.stableOperationNatTrans d

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- The actual supported middle row is exact in each nonnegative stable degree. -/
theorem boundedFlatCoefficientSupportedMiddleSequence_exact (n : ℕ) :
    (boundedFlatCoefficientSupportedMiddleSequence f (n : ℤ)).Exact := by
  apply middleComplex_exact_of_pointwise
  intro a
  exact (ShortComplex.ab_exact_iff_function_exact _).mp
    (boundedFlatCoefficientSupportedStageZeroChart_exact f a n)

/-- The specified inverse section followed by the original quotient is the proved isomorphism.
-/
instance boundedFlatCoefficientSupportedInverseSectionQuotient_isIso (n : ℕ) :
    IsIso (boundedFlatCoefficientSupportedInverseUnitSection f (n : ℤ) ≫
      contractionπ (underToLaurent R) (underToLaurentInvert R)
        (boundedFlatCoefficientSupportedStableGroupFunctor f ((n : ℤ) + 1))) :=
  boundedFlatCoefficientSupportedInverseUnitQuotient_isIso f n

/-- The natural boundary determined by the original inverse unit and the original quotient. -/
def boundedFlatCoefficientSupportedCanonicalBoundary (n : ℕ) :
    laurentUnderFunctor R ⋙ boundedFlatCoefficientSupportedStableGroupFunctor f ((n : ℤ) + 1) ⟶
      boundedFlatCoefficientSupportedStableGroupFunctor f (n : ℤ) :=
  unitQuotientBoundary (underToLaurent R) (underToLaurentInvert R)
    (boundedFlatCoefficientSupportedStableGroupFunctor f ((n : ℤ) + 1))
    (boundedFlatCoefficientSupportedStableGroupFunctor f (n : ℤ))
    (boundedFlatCoefficientSupportedInverseUnitSection f (n : ℤ))

/-- The specified original inverse unit splits this same canonical quotient boundary. -/
@[reassoc (attr := simp)]
theorem boundedFlatCoefficientSupportedInverseUnitSection_boundary (n : ℕ) :
    boundedFlatCoefficientSupportedInverseUnitSection f (n : ℤ) ≫
      boundedFlatCoefficientSupportedCanonicalBoundary f n = 𝟙 _ :=
  section_unitQuotientBoundary (underToLaurent R) (underToLaurentInvert R)
    (boundedFlatCoefficientSupportedStableGroupFunctor f ((n : ℤ) + 1))
    (boundedFlatCoefficientSupportedStableGroupFunctor f (n : ℤ))
    (boundedFlatCoefficientSupportedInverseUnitSection f (n : ℤ))

/-- The original corner quotient, Laurent group and coefficient group form a genuinely split
natural boundary row. -/
def boundedFlatCoefficientSupportedBoundarySplitting (n : ℕ) :
    (splitUnitQuotientBoundarySequence (polynomialUnderCoefficient R) (underToLaurent R)
      (underToLaurentInvert R) (boundedFlatCoefficientSupportedCommonCorner (R := R))
      (boundedFlatCoefficientSupportedStableGroupFunctor f ((n : ℤ) + 1))
      (boundedFlatCoefficientSupportedStableGroupFunctor f (n : ℤ))
      (boundedFlatCoefficientSupportedInverseUnitSection f (n : ℤ))).Splitting := by
  apply unitQuotientBoundarySplitting
  exact boundedFlatCoefficientSupportedMiddleSequence_exact f (n + 1)

/-- Every additive endofunctor preserves this original positive supported middle row by its two
constructed splittings. -/
theorem boundedFlatCoefficientSupportedMiddleSequence_map_exact (n : ℕ)
    (T : (Under R ⥤ AddCommGrpCat.{u + 1}) ⥤ (Under R ⥤ AddCommGrpCat.{u + 1}))
    [T.Additive] : ((boundedFlatCoefficientSupportedMiddleSequence f ((n : ℤ) + 1)).map T).Exact :=
  middleComplex_map_exact (polynomialUnderCoefficient R) (underToLaurent R)
    (underToLaurentInvert R) (boundedFlatCoefficientSupportedCommonCorner (R := R))
    (boundedFlatCoefficientSupportedStableGroupFunctor f ((n : ℤ) + 1))
    (boundedFlatCoefficientSupportedStableGroupFunctor f (n : ℤ))
    (boundedFlatCoefficientSupportedInverseUnitSection f (n : ℤ))
    (polynomialUnderZeroNat R) (polynomialUnderCoefficient_zeroNat R)
    (boundedFlatCoefficientSupportedMiddleSequence_exact f (n + 1)) T

end Quillen.PerfectComplexes
