/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryPerfectBoundaryProjection

/-! Original auxiliary-supported boundary classes under both actual coefficient projections. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.PerfectComplexes Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace QuillenTest.AuxiliaryPerfectBoundaryProjection
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

/-- The original K1 class has its original union-supported K0 boundary under projection. -/
theorem original_Kone_boundary_projected_Kzero
    (a : Under R)
    (x : PerfectSupportedK (f.left ⁻¹ᵁ T).ι ((0 : ℕ) + 1)) :
    let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
    let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
    let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
    boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a ((0 : ℕ) : ℤ)
      (eqToHom (congrArg (stableHomotopyGroup
        ((boundedFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T).obj a))
        (show ((0 + 1 : ℕ) : ℤ) = (0 : ℤ) + 1 from rfl))
        ((stableHomotopyFunctor (((0 : ℕ) + 1 : ℕ) : ℤ)).map
          ((boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a)
          (auxiliaryOpenPerfectStableEquiv f T a ((0 : ℕ) + 1)
            (Additive.ofMul (perfectSupportedKPullback
              (qcSupportedBaseSquare (supportedPairTargetSquare (schemeMap f a) f.left
                (supportRestrictionPair (projection (op Q, a)) T)
                (projection (op P, a)) (schemeMap_projection f a))) ((0 : ℕ) + 1) x))))) =
      -((stableHomotopyFunctor ((0 : ℕ) : ℤ)).map
        ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)
        (auxiliaryFiberPerfectStableEquiv f T a (0 : ℕ)
          (Additive.ofMul (perfectSupportedKPullback
            (qcSupportedBaseSquare (supportedPairUnionSquare (schemeMap f a) f.left
              (supportRestrictionPair (projection (op Q, a)) T)
              (projection (op P, a)) (schemeMap_projection f a))) (0 : ℕ)
            (qcqsPerfectSupportedConnectingHom f.left T
              (isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace T)))
              (0 : ℕ) x))))) := by
  exact boundedFlatCoefficientAuxiliaryFineConnecting_originalPerfectClass_sign f T a 0 rfl x

end QuillenTest.AuxiliaryPerfectBoundaryProjection
