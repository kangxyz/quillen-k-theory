/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryFinePerfectConnecting
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.PairNaturality

/-!
# Original auxiliary perfect boundaries under the actual coefficient projection

The actual coefficient projection and its original inverse-image and union-support
pair squares preserve the original geometric boundary. Their unchanged pullbacks
then identify the intrinsic auxiliary fine boundary on every original perfect
class, with its explicit single negative sign. No isomorphism of independently
chosen zero objects or replacement connecting map is used.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

/-- The original supported geometric boundary preserves both actual coefficient projections. -/
theorem boundedFlatCoefficientAuxiliaryPerfectConnecting_projection
    (a : Under R) (n : ℕ) (x : PerfectSupportedK (f.left ⁻¹ᵁ T).ι (n + 1)) :
    let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
    let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
    let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
    perfectSupportedKPullback
      (qcSupportedBaseSquare (supportedPairUnionSquare (schemeMap f a) f.left
        (supportRestrictionPair (projection (op Q, a)) T)
        (projection (op P, a)) (schemeMap_projection f a))) n
      (qcqsPerfectSupportedConnectingHom f.left T
        (isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace T))) n x) =
    qcqsPerfectSupportedConnectingHom (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a)
      (isCompact_iff_compactSpace.mpr
        (boundedFlatCoefficientSupportOpen_compactSpace Q T a)) n
      (perfectSupportedKPullback
        (qcSupportedBaseSquare (supportedPairTargetSquare (schemeMap f a) f.left
          (supportRestrictionPair (projection (op Q, a)) T)
          (projection (op P, a)) (schemeMap_projection f a))) (n + 1) x) := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  exact DFunLike.congr_fun (qcqsPerfectSupportedConnectingHom_pullback
    (schemeMap f a) f.left (supportRestrictionPair (projection (op Q, a)) T)
    (projection (op P, a)) (schemeMap_projection f a)
    (isCompact_iff_compactSpace.mpr (boundedFlatCoefficientSupportOpen_compactSpace Q T a))
    (isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace T))) n) x

/-- Every original supported perfect class retains the actual projection and intrinsic boundary. -/
theorem boundedFlatCoefficientAuxiliaryFineConnecting_originalPerfectClass_sign
    (a : Under R) (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : PerfectSupportedK (f.left ⁻¹ᵁ T).ι (n + 1)) :
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
                (projection (op P, a)) (schemeMap_projection f a))) (n + 1) x))))) =
      -((stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)
        (auxiliaryFiberPerfectStableEquiv f T a n
          (Additive.ofMul (perfectSupportedKPullback
            (qcSupportedBaseSquare (supportedPairUnionSquare (schemeMap f a) f.left
              (supportRestrictionPair (projection (op Q, a)) T)
              (projection (op P, a)) (schemeMap_projection f a))) n
            (qcqsPerfectSupportedConnectingHom f.left T
              (isCompact_iff_compactSpace.mpr (inferInstanceAs (CompactSpace T))) n x))))) := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  have hs := boundedFlatCoefficientAuxiliaryFineConnecting_perfectClass_sign f T a n κ
    (perfectSupportedKPullback
      (qcSupportedBaseSquare (supportedPairTargetSquare (schemeMap f a) f.left
        (supportRestrictionPair (projection (op Q, a)) T)
        (projection (op P, a)) (schemeMap_projection f a))) (n + 1) x)
  have hp := boundedFlatCoefficientAuxiliaryPerfectConnecting_projection f T a n x
  dsimp only at hs hp ⊢
  exact hs.trans (congrArg (fun y => -((stableHomotopyFunctor (n : ℤ)).map
    ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)
    (auxiliaryFiberPerfectStableEquiv f T a n (Additive.ofMul y)))) hp.symm)

end Quillen.PerfectComplexes
