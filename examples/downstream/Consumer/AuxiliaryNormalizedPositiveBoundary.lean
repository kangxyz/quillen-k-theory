/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryNormalizedRowPositiveBoundary

/-!
Original ambient supported perfect restrictions lie in the kernel of the
intrinsic normalized auxiliary boundary in every positive source degree.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.PerfectComplexes ParameterAuxiliaryNormalizedRowLocalization
open GlobalSectionChangeIndex ParameterAuxiliarySupport
universe u
namespace Consumer.AuxiliaryNormalizedPositiveBoundary
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

/-- Actual supported restriction is annihilated by the intrinsic normalized row boundary. -/
theorem normalizedBoundary_originalSupportedRestriction_eq_zero
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : PerfectSupportedK (boundedFlatCoefficientSupportOpen Q T a).ι (n + 1)) :
    normalizedPresentationConnecting f T a (n : ℤ)
      (eqToHom (congrArg (stableHomotopyGroup
        (ParameterTensorNormalizedRowPresentation.supported (inverseOpen f.left T).ι
          (specUnder.obj a))) κ)
        ((normalizedFineOpenComparison f T a ((n + 1 : ℕ) : ℤ)).inv
          ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
            ((boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a)
            (auxiliaryOpenPerfectStableEquiv f T a (n + 1)
              (Additive.ofMul (perfectSupportedKRestrict (schemeMap f a)
                (boundedFlatCoefficientSupportOpen Q T a) (n + 1) x)))))) = 0 := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  have hm : perfectSupportedKRestrict (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a) (n + 1) x ∈
      (perfectSupportedKRestrict (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a) (n + 1)).range := ⟨x, rfl⟩
  rw [range_qcqs_perfectSupportedKRestrict_eq_ker_qcqsPerfectSupportedConnectingHom
    (schemeMap f a) (boundedFlatCoefficientSupportOpen Q T a)
    (isCompact_iff_compactSpace.mpr (boundedFlatCoefficientSupportOpen_compactSpace Q T a)) n] at hm
  have hz : qcqsPerfectSupportedConnectingHom (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a)
      (isCompact_iff_compactSpace.mpr (boundedFlatCoefficientSupportOpen_compactSpace Q T a)) n
      (perfectSupportedKRestrict (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a) (n + 1) x) = 1 := hm
  have h := normalizedPresentationConnecting_perfectClass_sign f T a n κ
    (perfectSupportedKRestrict (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a) (n + 1) x)
  dsimp only at h
  rw [hz, ofMul_one, map_zero, map_zero, neg_zero] at h
  exact (ConcreteCategory.bijective_of_isIso
    (normalizedFineSupportComparison f T a (n : ℤ)).hom).injective
    (h.trans (map_zero _).symm)

end Consumer.AuxiliaryNormalizedPositiveBoundary
