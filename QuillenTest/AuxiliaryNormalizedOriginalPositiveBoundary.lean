/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryNormalizedRowOriginalPositiveBoundary

/-!
The original supported K-zero kernel maps into the kernel of the intrinsic
normalized auxiliary boundary through the actual coefficient projections.
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
namespace QuillenTest.AuxiliaryNormalizedOriginalPositiveBoundary

private theorem zero_of_signed_image {A B : AddCommGrpCat.{u}} {C : Type*} [One C]
    (s : A ≅ B) (a : A) (g : C → B) (c : C)
    (h : s.hom a = -g c) (hg : g 1 = 0) (hc : c = 1) : a = 0 := by
  apply (ConcreteCategory.bijective_of_isIso s.hom).injective
  calc
    s.hom a = -g c := h
    _ = 0 := by rw [hc, hg, neg_zero]
    _ = s.hom 0 := (map_zero _).symm

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

/-- The original supported K-zero kernel survives the actual projection and normalized boundary. -/
theorem normalized_original_Kzero_kernel
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (x : PerfectSupportedK (f.left ⁻¹ᵁ T).ι (0 + 1))
    (hx : qcqsPerfectSupportedConnectingHom f.left T
      (isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace T))) 0 x = 1) :
    let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
    let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
    let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
    normalizedPresentationConnecting f T a ((0 : ℕ) : ℤ)
      (eqToHom (congrArg (stableHomotopyGroup
        (ParameterTensorNormalizedRowPresentation.supported (inverseOpen f.left T).ι
          (specUnder.obj a))) (show ((0 + 1 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) + 1 from rfl))
        ((normalizedFineOpenComparison f T a ((0 + 1 : ℕ) : ℤ)).inv
          ((stableHomotopyFunctor ((0 + 1 : ℕ) : ℤ)).map
            ((boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a)
            (auxiliaryOpenPerfectStableEquiv f T a (0 + 1)
              (Additive.ofMul (perfectSupportedKPullback
                (qcSupportedBaseSquare (supportedPairTargetSquare (schemeMap f a) f.left
                  (supportRestrictionPair (projection (op Q, a)) T)
                  (projection (op P, a)) (schemeMap_projection f a))) (0 + 1) x)))))) = 0 := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  have h := normalizedPresentationConnecting_originalPerfectClass_sign f T a 0 rfl x
  dsimp only at h ⊢
  exact zero_of_signed_image
    (normalizedFineSupportComparison f T a ((0 : ℕ) : ℤ)) _
    (fun y => (stableHomotopyFunctor ((0 : ℕ) : ℤ)).map
      ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)
      (auxiliaryFiberPerfectStableEquiv f T a 0
        (Additive.ofMul (perfectSupportedKPullback
          (qcSupportedBaseSquare (supportedPairUnionSquare (schemeMap f a) f.left
            (supportRestrictionPair (projection (op Q, a)) T)
            (projection (op P, a)) (schemeMap_projection f a))) 0 y)))) _ h
    (by simp only [map_one, ofMul_one, map_zero]) hx

end QuillenTest.AuxiliaryNormalizedOriginalPositiveBoundary
