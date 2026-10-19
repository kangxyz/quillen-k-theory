/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryInitialPerfectConnecting
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryInitialTelescopeConnecting
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryPerfectClasses
public import Quillen.AlgebraicGeometry.PerfectComplexes.SupportedOpen.GlobalLocalization

/-!
# The original supported perfect boundary in the auxiliary telescope

The unchanged fine telescope boundary retains the original inverse-open supported perfect
boundary with the explicit negative stabilization sign. The proof uses the
original initial inclusion, whole null, coarse-to-full-open restriction and
positive cofinality, retaining both original perfect comparison classes.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes

private theorem stableMap_cast {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    {d e : ℤ} (h : d = e) :
    eqToHom (congrArg (stableHomotopyGroup E) h) ≫ (stableHomotopyFunctor e).map f =
      (stableHomotopyFunctor d).map f ≫ eqToHom (congrArg (stableHomotopyGroup F) h) := by
  subst e
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

/-- On original coarse representatives, the actual fine boundary retains its geometric sign. -/
theorem boundedFlatCoefficientAuxiliaryFineConnecting_relativePerfect_sign
    (a : Under R) (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : (boundedFlatCoefficientSupportedOpenModel f T a).waldhausen.K (n + 1)) :
    boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a (n : ℤ)
        ((stableHomotopyFunctor ((n : ℤ) + 1)).map
          ((boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a)
          (eqToHom (congrArg (stableHomotopyGroup
            ((boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T).obj a)) κ)
            (modelKStableEquiv (boundedFlatCoefficientSupportedFullOpenModel f T a) (n + 1)
              (Additive.ofMul (KMap (boundedFlatCoefficientSupportedOpenRestriction_exact f T a)
                (n + 1) x))))) =
      -((stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)
        (auxiliaryFiberPerfectStableEquiv f T a n
          (Additive.ofMul (perfectSupportedOpenConnectingHom (schemeMap f a)
            (boundedFlatCoefficientSupportOpen Q T a) n
            (boundedFlatCoefficientSupportedOpenPerfectKEquiv f T a (n + 1) x))))) := by
  let := boundedFlatCoefficientAuxiliaryInitialFiberLift_isStableEquivalence f T a (n : ℤ)
  let z := eqToHom (congrArg (stableHomotopyGroup
    ((boundedFlatCoefficientSupportedOpenPrespectrumFunctor f T).obj a)) κ)
    (modelKStableEquiv (boundedFlatCoefficientSupportedOpenModel f T a) (n + 1) (Additive.ofMul x))
  have h := ConcreteCategory.congr_hom
    (boundedFlatCoefficientAuxiliaryInitialConnecting_telescope f T a (n : ℤ)) z
  have ho := congrArg (stableHomotopyFunctor ((n : ℤ) + 1)).map
    (NatTrans.congr_app
      (boundedFlatCoefficientSupportedOpenBassTelescopeInclusion_restriction f T 0) a)
  have hs := ho.trans ((stableHomotopyFunctor ((n : ℤ) + 1)).map_comp
    ((boundedFlatCoefficientSupportedOpenBassRestriction f T 0).app a)
    ((boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a))
  have ht := (congrArg (boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a (n : ℤ))
    (ConcreteCategory.congr_hom hs z)).symm.trans h.symm
  have hn := modelKStableEquiv_naturality
    (boundedFlatCoefficientSupportedOpenRestrictionModelMap f T a)
    (n + 1) x
  have hc := ConcreteCategory.congr_hom
    (stableMap_cast
      (prespectrumMap (boundedFlatCoefficientSupportedOpenRestrictionModelMap f T a)) κ)
    (modelKStableEquiv (boundedFlatCoefficientSupportedOpenModel f T a) (n + 1) (Additive.ofMul x))
  have hr := hc.trans (congrArg
    (eqToHom (congrArg (stableHomotopyGroup
      ((boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T).obj a)) κ)) hn.symm)
  have hi := boundedFlatCoefficientAuxiliaryInitialConnecting_perfect_sign f T a n κ x
  dsimp only at h hi
  change (stableHomotopyFunctor ((n : ℤ) + 1)).map
    ((boundedFlatCoefficientSupportedOpenBassRestriction f T 0).app a) z = _ at hr
  simp only [ConcreteCategory.comp_apply] at ht
  rw [hr] at ht
  change _ = (stableHomotopyFunctor (n : ℤ)).map
    ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a) _ at ht
  exact ht.trans ((congrArg
    ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)) hi).trans
        (map_neg _ _))

/-- Every original inverse-open supported perfect class retains its geometric boundary and sign. -/
theorem boundedFlatCoefficientAuxiliaryFineConnecting_perfect_sign
    (a : Under R) (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : PerfectSupportedK (boundedFlatCoefficientOpenSupportOpen f T a).ι (n + 1)) :
    let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
    let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
    let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
    boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a (n : ℤ)
        ((stableHomotopyFunctor ((n : ℤ) + 1)).map
          ((boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a)
          (eqToHom (congrArg (stableHomotopyGroup
            ((boundedFlatCoefficientSupportedFullOpenPrespectrumFunctor f T).obj a)) κ)
            (auxiliaryOpenPerfectStableEquiv f T a (n + 1)
              (Additive.ofMul x)))) =
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
  obtain ⟨y, rfl⟩ := (auxiliaryOpenPerfectKEquiv f T a (n + 1)).surjective x
  obtain ⟨z, rfl⟩ :=
    (boundedFlatCoefficientSupportedOpenRestriction_KMap_succ_bijective f T a n).surjective y
  rw [auxiliaryOpenPerfectStableEquiv_evaluation]
  have he : qcqsPerfectSupportedConnectingHom (schemeMap f a)
            (boundedFlatCoefficientSupportOpen Q T a)
            (isCompact_iff_compactSpace.mpr
              (boundedFlatCoefficientSupportOpen_compactSpace Q T a)) n
      (auxiliaryOpenPerfectKEquiv f T a (n + 1)
        (KMap (boundedFlatCoefficientSupportedOpenRestriction_exact f T a) (n + 1) z)) =
      perfectSupportedOpenConnectingHom (schemeMap f a)
            (boundedFlatCoefficientSupportOpen Q T a) n
        (boundedFlatCoefficientSupportedOpenPerfectKEquiv f T a (n + 1) z) := by
    change qcqsPerfectSupportedConnectingHom (schemeMap f a)
            (boundedFlatCoefficientSupportOpen Q T a)
            (isCompact_iff_compactSpace.mpr
              (boundedFlatCoefficientSupportOpen_compactSpace Q T a)) n
      (boundedFlatCoefficientSupportedFullOpenPerfectKEquiv f T a (n + 1)
        (KMap (boundedFlatCoefficientSupportedOpenRestriction_exact f T a) (n + 1) z)) = _
    rw [boundedFlatCoefficientSupportedOpenRestriction_perfectKComparison]
    exact DFunLike.congr_fun (qcqsPerfectSupportedConnectingHom_comp_relative (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a)
      (isCompact_iff_compactSpace.mpr (boundedFlatCoefficientSupportOpen_compactSpace Q T a)) n)
      (boundedFlatCoefficientSupportedOpenPerfectKEquiv f T a (n + 1) z)
  rw [he]
  exact boundedFlatCoefficientAuxiliaryFineConnecting_relativePerfect_sign f T a n κ z

/-- The same formula retains the original telescope perfect class before its degree cast. -/
theorem boundedFlatCoefficientAuxiliaryFineConnecting_perfectClass_sign
    (a : Under R) (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : PerfectSupportedK (boundedFlatCoefficientOpenSupportOpen f T a).ι (n + 1)) :
    let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
    let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
    let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
    boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup
          ((boundedFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T).obj a)) κ)
          ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
            ((boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a)
            (auxiliaryOpenPerfectStableEquiv f T a (n + 1)
              (Additive.ofMul x)))) =
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
  have hc := ConcreteCategory.congr_hom
    (stableMap_cast ((boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a) κ)
    (auxiliaryOpenPerfectStableEquiv f T a (n + 1) (Additive.ofMul x))
  exact (congrArg
    (boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a (n : ℤ)) hc.symm).trans
    (boundedFlatCoefficientAuxiliaryFineConnecting_perfect_sign f T a n κ x)

end Quillen.PerfectComplexes
