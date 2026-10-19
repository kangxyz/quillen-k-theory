/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryNormalizedRowBoundaryComparison
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryFinePerfectConnecting

/-!
# Original positive supported boundaries in the normalized auxiliary row

The intrinsic normalized row boundary carries the original supported perfect
boundary with its explicit negative sign in every nonnegative degree. Both the
inverse-comparison expression for every perfect class and the actual finite
normalized Model class retain the inverse-open and union-open supports, the
original coefficient restriction, stage-zero inclusions and signed-degree cast.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
universe u
namespace Quillen.PerfectComplexes.ParameterAuxiliaryNormalizedRowLocalization
open GlobalSectionChangeIndex ParameterAuxiliarySupport GlobalAuxiliaryParameterCoefficient

private theorem comparison_cast {E F : LoopPrespectrum.{u}}
    (e : ∀ d : ℤ, stableHomotopyGroup E d ≅ stableHomotopyGroup F d)
    {d k : ℤ} (h : d = k) (x : stableHomotopyGroup E d) :
    (e k).hom (eqToHom (congrArg (stableHomotopyGroup E) h) x) =
      eqToHom (congrArg (stableHomotopyGroup F) h) ((e d).hom x) := by
  subst k
  rfl

private theorem boundary_class_sign {E F S T : LoopPrespectrum.{u}}
    (e : ∀ d : ℤ, stableHomotopyGroup E d ≅ stableHomotopyGroup F d)
    {m k d : ℤ} (κ : m = k)
    (s : stableHomotopyGroup S d ≅ stableHomotopyGroup T d)
    (δ : stableHomotopyGroup E k ⟶ stableHomotopyGroup S d)
    (δf : stableHomotopyGroup F k ⟶ stableHomotopyGroup T d)
    (x : stableHomotopyGroup E m) (y : stableHomotopyGroup F m)
    (z : stableHomotopyGroup T d)
    (hδ : δ ≫ s.hom = (e k).hom ≫ δf)
    (hx : (e m).hom x = y)
    (hs : δf (eqToHom (congrArg (stableHomotopyGroup F) κ) y) = -z) :
    s.hom (δ (eqToHom (congrArg (stableHomotopyGroup E) κ) x)) = -z := by
  have hb := ConcreteCategory.congr_hom hδ
    (eqToHom (congrArg (stableHomotopyGroup E) κ) x)
  simp only [ConcreteCategory.comp_apply] at hb
  have hc := (comparison_cast e κ x).trans
    (congrArg (eqToHom (congrArg (stableHomotopyGroup F) κ)) hx)
  exact hb.trans ((congrArg δf hc).trans hs)

variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

/-- Every original supported perfect class retains its boundary and explicit negative sign. -/
theorem normalizedPresentationConnecting_perfectClass_sign
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : PerfectSupportedK (boundedFlatCoefficientOpenSupportOpen f T a).ι (n + 1)) :
    let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
    let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
    let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
    (normalizedFineSupportComparison f T a (n : ℤ)).hom
      (normalizedPresentationConnecting f T a (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup
          (ParameterTensorNormalizedRowPresentation.supported (inverseOpen f.left T).ι
            (specUnder.obj a))) κ)
          ((normalizedFineOpenComparison f T a ((n + 1 : ℕ) : ℤ)).inv
            ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
              ((boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a)
              (auxiliaryOpenPerfectStableEquiv f T a (n + 1) (Additive.ofMul x)))))) =
      -((stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)
        (auxiliaryFiberPerfectStableEquiv f T a n
          (Additive.ofMul (qcqsPerfectSupportedConnectingHom (schemeMap f a)
            (boundedFlatCoefficientSupportOpen Q T a)
            (isCompact_iff_compactSpace.mpr
              (boundedFlatCoefficientSupportOpen_compactSpace Q T a)) n x)))) := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  dsimp only
  exact boundary_class_sign (normalizedFineOpenComparison f T a) κ
    (normalizedFineSupportComparison f T a (n : ℤ))
    (normalizedPresentationConnecting f T a (n : ℤ))
    (boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a (n : ℤ))
    _ _ _ (normalizedPresentationConnecting_fine f T a (n : ℤ))
    (Iso.inv_hom_id_apply _ _)
    (boundedFlatCoefficientAuxiliaryFineConnecting_perfectClass_sign f T a n κ x)

/-- The actual finite normalized class retains the original restriction and supported boundary. -/
theorem normalizedPresentationConnecting_normalizedModelClass_sign
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (z : ((openModel f.left T).obj (specUnder.obj a)).waldhausen.K (n + 1)) :
    let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
    let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
    let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
    (normalizedFineSupportComparison f T a (n : ℤ)).hom
      (normalizedPresentationConnecting f T a (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup
          (ParameterTensorNormalizedRowPresentation.supported (inverseOpen f.left T).ι
            (specUnder.obj a))) κ)
          (SchemeModelRowSeed.normalizedModelClass (openModel f.left T)
            (ParameterLaurentTrack.supportedUnit (inverseOpen f.left T).ι)
            (ParameterLaurentTrack.supportedUnit_naturality (inverseOpen f.left T).ι)
            (specUnder.obj a) (n + 1) z))) =
      -((stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)
        (auxiliaryFiberPerfectStableEquiv f T a n
          (Additive.ofMul (qcqsPerfectSupportedConnectingHom (schemeMap f a)
            (boundedFlatCoefficientSupportOpen Q T a)
            (isCompact_iff_compactSpace.mpr
              (boundedFlatCoefficientSupportOpen_compactSpace Q T a)) n
            (auxiliaryOpenPerfectKEquiv f T a (n + 1)
              (Quillen.Waldhausen.KMap ((openComparison f T).app a).exact (n + 1) z)))))) := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  dsimp only
  exact boundary_class_sign (normalizedFineOpenComparison f T a) κ
    (normalizedFineSupportComparison f T a (n : ℤ))
    (normalizedPresentationConnecting f T a (n : ℤ))
    (boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a (n : ℤ))
    _ _ _ (normalizedPresentationConnecting_fine f T a (n : ℤ))
    (normalized_fine_open_perfectClass f T a (n + 1) z)
    (boundedFlatCoefficientAuxiliaryFineConnecting_perfectClass_sign f T a n κ
      (auxiliaryOpenPerfectKEquiv f T a (n + 1)
        (Quillen.Waldhausen.KMap ((openComparison f T).app a).exact (n + 1) z)))

end Quillen.PerfectComplexes.ParameterAuxiliaryNormalizedRowLocalization
