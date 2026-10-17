/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedMiddleIteration

/-!
# Exact original supported negative middle rows

The original supported K-zero comparison and the actual inverse-unit quotient identify K-zero
with one contraction of the original supported K-one pair functor. Iterating the same original
pair contraction and its coefficient transport identifies every original supported Bass group
with the corresponding K-one iterate. The two constructed split rows and actual independent
pair-variable interchange then give middle exactness. The ambient scheme is qcqs and the
removed open is compact; no supported localization theorem is inferred from ambient groups.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent Quillen.Bass.TwoChart Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]
local notation "Ip" => iteratedContractionFunctor
  (NatTrans.op Scheme.Bass.pairPlus) (NatTrans.op Scheme.Bass.pairMinus)
local notation "Bu" => contractionFunctor (underToLaurent R) (underToLaurentInvert R)
local notation "K1" => Bass.supportedKAddFunctor 1

/-- Original supported K-zero is one actual contraction of original supported K-one. -/
def boundedFlatCoefficientSupportedKZeroContractionIso :
    boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedKZeroFunctor ≅
      boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ (Ip 1).obj K1 := by
  let : IsIso (boundedFlatCoefficientSupportedInverseUnitQuotient f 0) :=
    boundedFlatCoefficientSupportedInverseUnitQuotient_isIso f 0
  exact boundedFlatCoefficientSupportedBassBottomZeroNatIso f ≪≫
    asIso (boundedFlatCoefficientSupportedInverseUnitQuotient f 0) ≪≫
      (Bu).mapIso (boundedFlatCoefficientSupportedKStableNatIso f 1).symm ≪≫
        boundedFlatCoefficientSupportedContractionTransportIso f K1

/-- Every original supported negative group retains its actual iterated K-one presentation. -/
def boundedFlatCoefficientSupportedNegativeIteratedKOneIso :
    (i : ℕ) → boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedNegativeKFunctor i ≅
      boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ (Ip (i + 1)).obj K1
  | 0 => boundedFlatCoefficientSupportedKZeroContractionIso f
  | i + 1 =>
    (boundedFlatCoefficientSupportedContractionTransportIso f
      (Bass.supportedNegativeKFunctor i)).symm ≪≫
      (Bu).mapIso (boundedFlatCoefficientSupportedNegativeIteratedKOneIso i) ≪≫
        boundedFlatCoefficientSupportedContractionTransportIso f ((Ip (i + 1)).obj K1)

/-- The original supported common-corner and signed difference row is exact in every negative
Bass degree on the actual coefficient pair family. -/
theorem boundedFlatCoefficientSupportedNegativeMiddle_exact (i : ℕ) :
    (middleComplex (polynomialUnderCoefficient R) (underToLaurent R)
      (underToLaurentInvert R) (boundedFlatCoefficientSupportedCommonCorner (R := R))
      (boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedNegativeKFunctor i)).Exact :=
  ShortComplex.exact_of_iso
    ((middleIso (polynomialUnderCoefficient R) (underToLaurent R)
      (underToLaurentInvert R) (boundedFlatCoefficientSupportedCommonCorner (R := R))
      (boundedFlatCoefficientSupportedNegativeIteratedKOneIso f i)) ≪≫
        boundedFlatCoefficientSupportedMiddleTransportIso f ((Ip (i + 1)).obj K1)).symm
    (boundedFlatCoefficientSupportedRestrictedMiddle_iteratedK_exact f 0 (i + 1))

end Quillen.PerfectComplexes
