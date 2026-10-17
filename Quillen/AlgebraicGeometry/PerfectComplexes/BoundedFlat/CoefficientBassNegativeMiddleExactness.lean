/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassMiddleIteration
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassKZeroComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientKStableComparison

/-!
# Middle exactness for the original negative Bass groups on qcqs coefficient families

Original perfect K-zero, its actual bounded-flat comparison, and the original inverse-unit
quotient identify K-zero naturally with one contraction of K-one. All subsequent comparisons
use only the original contraction functor and actual native coefficient transport. Thus the
already proved exact iterated positive middle rows give middle exactness for the unchanged
negative groups. No higher-stage unit identification or replacement boundary is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent Quillen.Bass.TwoChart Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]
variable [QuasiSeparatedSpace P.left]
local notation "Is" => iteratedContractionFunctor
  (NatTrans.op Scheme.PolynomialLaurent.Relative.plus)
  (NatTrans.op Scheme.PolynomialLaurent.Relative.minus)
local notation "K1" => Scheme.quasiCompactSchemeProperty.ι.op ⋙ boundedFlatPerfectKAddFunctor 1

/-- The original perfect K-zero is one genuine contraction of the original bounded-flat K-one.
-/
def boundedFlatCoefficientPerfectKZeroContractionIso :
    boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.perfectKZeroFunctor ≅
      boundedFlatCoefficientQuasiCompactRow P ⋙ (Is 1).obj K1 :=
  boundedFlatCoefficientAmbientBassBottomZeroNatIso P ≪≫
    (boundedFlatCoefficientSectionKStableNatIso P 0).symm ≪≫
    asIso (boundedFlatCoefficientInverseUnitQuotient P 0) ≪≫
    boundedFlatCoefficientContractionTransportIso P K1

/-- All original negative groups agree naturally with the actual iterated K-one contractions.
-/
def boundedFlatCoefficientNegativeIteratedKOneIso :
    (i : ℕ) → boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor i ≅
      boundedFlatCoefficientQuasiCompactRow P ⋙ (Is (i + 1)).obj K1
  | 0 => boundedFlatCoefficientPerfectKZeroContractionIso P
  | i + 1 => (boundedFlatCoefficientContractionTransportIso P (Bass.negativeKFunctor i)).symm ≪≫
      (contractionFunctor (underToLaurent R) (underToLaurentInvert R)).mapIso
        (boundedFlatCoefficientNegativeIteratedKOneIso i) ≪≫
      boundedFlatCoefficientContractionTransportIso P ((Is (i + 1)).obj K1)

/-- The unchanged common-corner and signed difference row is exact in every negative degree.
-/
theorem boundedFlatCoefficientNegativeMiddle_exact (i : ℕ) :
    (middleComplex (polynomialUnderCoefficient R) (underToLaurent R)
      (underToLaurentInvert R) (boundedFlatCoefficientCommonCorner (R := R))
      (boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor i)).Exact :=
  ShortComplex.exact_of_iso
    ((middleIso (polynomialUnderCoefficient R) (underToLaurent R)
      (underToLaurentInvert R) (boundedFlatCoefficientCommonCorner (R := R))
      (boundedFlatCoefficientNegativeIteratedKOneIso P i)) ≪≫
        boundedFlatCoefficientMiddleTransportIso P ((Is (i + 1)).obj K1)).symm
    (boundedFlatCoefficientRestrictedMiddle_iteratedK_exact P 0 (i + 1))

end Quillen.PerfectComplexes
