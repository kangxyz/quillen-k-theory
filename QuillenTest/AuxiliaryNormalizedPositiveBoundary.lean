/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryNormalizedRowPositiveBoundary

/-!
The actual finite normalized K-one class and the original supported K-zero
boundary have equivalent vanishing after the prescribed union-support comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.PerfectComplexes ParameterAuxiliaryNormalizedRowLocalization
open GlobalSectionChangeIndex ParameterAuxiliarySupport GlobalAuxiliaryParameterCoefficient
universe u
namespace QuillenTest.AuxiliaryNormalizedPositiveBoundary
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

/-- The normalized K-one boundary detects vanishing of the original supported K-zero class. -/
theorem normalized_Kone_original_Kzero_vanishing
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (z : ((openModel f.left T).obj (specUnder.obj a)).waldhausen.K (0 + 1)) :
    let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
    let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
    let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
    (normalizedFineSupportComparison f T a ((0 : ℕ) : ℤ)).hom
      (normalizedPresentationConnecting f T a ((0 : ℕ) : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup
          (ParameterTensorNormalizedRowPresentation.supported (inverseOpen f.left T).ι
            (specUnder.obj a))) (show ((0 + 1 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) + 1 from rfl))
          (SchemeModelRowSeed.normalizedModelClass (openModel f.left T)
            (ParameterLaurentTrack.supportedUnit (inverseOpen f.left T).ι)
            (ParameterLaurentTrack.supportedUnit_naturality (inverseOpen f.left T).ι)
            (specUnder.obj a) (0 + 1) z))) = 0 ↔
      (stableHomotopyFunctor ((0 : ℕ) : ℤ)).map
        ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)
        (auxiliaryFiberPerfectStableEquiv f T a 0
          (Additive.ofMul (qcqsPerfectSupportedConnectingHom (schemeMap f a)
            (boundedFlatCoefficientSupportOpen Q T a)
            (isCompact_iff_compactSpace.mpr
              (boundedFlatCoefficientSupportOpen_compactSpace Q T a)) 0
            (auxiliaryOpenPerfectKEquiv f T a (0 + 1)
              (Quillen.Waldhausen.KMap ((openComparison f T).app a).exact (0 + 1) z))))) = 0 := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  have h := normalizedPresentationConnecting_normalizedModelClass_sign f T a 0 rfl z
  dsimp only at h ⊢
  rw [h, neg_eq_zero]

end QuillenTest.AuxiliaryNormalizedPositiveBoundary
