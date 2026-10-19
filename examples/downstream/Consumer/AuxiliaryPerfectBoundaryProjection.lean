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
namespace Consumer.AuxiliaryPerfectBoundaryProjection
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

/-- A zero original geometric boundary stays zero in the intrinsic coefficient fine row. -/
theorem original_boundary_zero_projects_to_fine_zero
    (a : Under R) (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : PerfectSupportedK (f.left ⁻¹ᵁ T).ι (n + 1))
    (hx : qcqsPerfectSupportedConnectingHom f.left T
      (isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace T))) n x = 1) :
    let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
    let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
    let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
    boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a (n : ℤ)
      (eqToHom (congrArg (stableHomotopyGroup
        ((boundedFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T).obj a)) κ)
        ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
          ((boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a)
          (auxiliaryOpenPerfectStableEquiv f T a (n + 1)
            (Additive.ofMul (perfectSupportedKPullback
              (qcSupportedBaseSquare (supportedPairTargetSquare (schemeMap f a) f.left
                (supportRestrictionPair (projection (op Q, a)) T)
                (projection (op P, a)) (schemeMap_projection f a))) (n + 1) x))))) = 0 := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  have hs := boundedFlatCoefficientAuxiliaryFineConnecting_originalPerfectClass_sign f T a n κ x
  dsimp only at hs ⊢
  rw [hs, hx]
  simp

end Consumer.AuxiliaryPerfectBoundaryProjection
