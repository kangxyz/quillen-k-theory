/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientInitialPerfectConnecting
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientInitialTelescopeConnecting
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterInitialAmbientPerfectClasses
public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalLocalization

/-!
# The original perfect boundary in the genuine fine telescope

The unchanged fine telescope boundary retains the original compact-open perfect
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
  [QuasiSeparatedSpace Q.left]

/-- On original coarse representatives, the actual fine boundary retains its geometric sign. -/
theorem boundedFlatCoefficientFineConnecting_relativePerfect_sign
    (a : Under R) (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : (boundedFlatCoefficientOpenModel f a).waldhausen.K (n + 1)) :
    boundedFlatCoefficientFineLocalizationConnecting f a (n : ℤ)
        ((stableHomotopyFunctor ((n : ℤ) + 1)).map
          ((boundedFlatCoefficientFullOpenBassTelescopeInclusion f 0).app a)
          (eqToHom (congrArg (stableHomotopyGroup
            ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj a)) κ)
            (modelKStableEquiv (boundedFlatCoefficientSectionModel (op P, a)) (n + 1)
              (Additive.ofMul (KMap (boundedFlatCoefficientOpenRestriction_exact f a)
                (n + 1) x))))) =
      -((stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a)
        (boundedFlatCoefficientSupportedKStableEquiv f a n
          (Additive.ofMul (perfectOpenConnectingHom (schemeMap f a) n
            (boundedFlatCoefficientOpenPerfectKEquiv f a (n + 1) x))))) := by
  let := boundedFlatCoefficientInitialFiberLift_isStableEquivalence f a (n : ℤ)
  let z := eqToHom (congrArg (stableHomotopyGroup
    ((boundedFlatCoefficientOpenPrespectrumFunctor f).obj a)) κ)
    (modelKStableEquiv (boundedFlatCoefficientOpenModel f a) (n + 1) (Additive.ofMul x))
  have h := ConcreteCategory.congr_hom
    (boundedFlatCoefficientInitialConnecting_telescope f a (n : ℤ)) z
  have ho := congrArg (stableHomotopyFunctor ((n : ℤ) + 1)).map
    (NatTrans.congr_app (boundedFlatCoefficientOpenBassTelescopeInclusion_restriction f 0) a)
  have hs := ho.trans ((stableHomotopyFunctor ((n : ℤ) + 1)).map_comp
    ((boundedFlatCoefficientOpenBassRestriction f 0).app a)
    ((boundedFlatCoefficientFullOpenBassTelescopeInclusion f 0).app a))
  have ht := (congrArg (boundedFlatCoefficientFineLocalizationConnecting f a (n : ℤ))
    (ConcreteCategory.congr_hom hs z)).symm.trans h.symm
  have hn := modelKStableEquiv_naturality (boundedFlatCoefficientOpenRestrictionModelMap f a)
    (n + 1) x
  have hc := ConcreteCategory.congr_hom
    (stableMap_cast (prespectrumMap (boundedFlatCoefficientOpenRestrictionModelMap f a)) κ)
    (modelKStableEquiv (boundedFlatCoefficientOpenModel f a) (n + 1) (Additive.ofMul x))
  have hr := hc.trans (congrArg
    (eqToHom (congrArg (stableHomotopyGroup
      ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj a)) κ)) hn.symm)
  have hi := boundedFlatCoefficientInitialConnecting_perfect_sign f a n κ x
  dsimp only at h hi
  change (stableHomotopyFunctor ((n : ℤ) + 1)).map
    ((boundedFlatCoefficientOpenBassRestriction f 0).app a) z = _ at hr
  simp only [ConcreteCategory.comp_apply] at ht
  rw [hr] at ht
  change _ = (stableHomotopyFunctor (n : ℤ)).map
    ((boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a) _ at ht
  exact ht.trans ((congrArg
    ((stableHomotopyFunctor (n : ℤ)).map
      ((boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a)) hi).trans
        (map_neg _ _))

/-- Every original compact-open perfect class has its unchanged geometric boundary with a minus. -/
theorem boundedFlatCoefficientFineConnecting_perfect_sign
    (a : Under R) (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : PerfectK (space (op P, a)) (n + 1)) :
    let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
    let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
    let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
    boundedFlatCoefficientFineLocalizationConnecting f a (n : ℤ)
        ((stableHomotopyFunctor ((n : ℤ) + 1)).map
          ((boundedFlatCoefficientFullOpenBassTelescopeInclusion f 0).app a)
          (eqToHom (congrArg (stableHomotopyGroup
            ((boundedFlatCoefficientFullOpenPrespectrumFunctor f).obj a)) κ)
            (boundedFlatCoefficientSectionPerfectKStableEquiv (op P, a) (n + 1)
              (Additive.ofMul x)))) =
      -((stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a)
        (boundedFlatCoefficientSupportedKStableEquiv f a n
          (Additive.ofMul (qcqsPerfectConnectingHom (schemeMap f a) n x)))) := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  dsimp only
  obtain ⟨y, rfl⟩ := (boundedFlatCoefficientSectionPerfectKEquiv (op P, a) (n + 1)).surjective x
  obtain ⟨z, rfl⟩ := (boundedFlatCoefficientOpenRestriction_KMap_succ_bijective f a n).surjective y
  rw [boundedFlatCoefficientSectionPerfectKStableEquiv_evaluation]
  have he : qcqsPerfectConnectingHom (schemeMap f a) n
      (boundedFlatCoefficientSectionPerfectKEquiv (op P, a) (n + 1)
        (KMap (boundedFlatCoefficientOpenRestriction_exact f a) (n + 1) z)) =
      perfectOpenConnectingHom (schemeMap f a) n
        (boundedFlatCoefficientOpenPerfectKEquiv f a (n + 1) z) := by
    change qcqsPerfectConnectingHom (schemeMap f a) n
      (boundedFlatCoefficientFullOpenPerfectKEquiv f a (n + 1)
        (KMap (boundedFlatCoefficientOpenRestriction_exact f a) (n + 1) z)) = _
    rw [boundedFlatCoefficientOpenRestriction_perfectKComparison]
    exact DFunLike.congr_fun (qcqsPerfectConnectingHom_comp_relative (schemeMap f a) n)
      (boundedFlatCoefficientOpenPerfectKEquiv f a (n + 1) z)
  rw [he]
  exact boundedFlatCoefficientFineConnecting_relativePerfect_sign f a n κ z

/-- The same formula retains the original telescope perfect class before its degree cast. -/
theorem boundedFlatCoefficientFineConnecting_perfectClass_sign
    (a : Under R) (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : PerfectK (space (op P, a)) (n + 1)) :
    let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
    let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
    let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
    boundedFlatCoefficientFineLocalizationConnecting f a (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup
          ((boundedFlatCoefficientFullOpenBassTelescopeFunctor f).obj a)) κ)
          ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
            ((boundedFlatCoefficientFullOpenBassTelescopeInclusion f 0).app a)
            (boundedFlatCoefficientSectionPerfectKStableEquiv (op P, a) (n + 1)
              (Additive.ofMul x)))) =
      -((stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a)
        (boundedFlatCoefficientSupportedKStableEquiv f a n
          (Additive.ofMul (qcqsPerfectConnectingHom (schemeMap f a) n x)))) := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  dsimp only
  have hc := ConcreteCategory.congr_hom
    (stableMap_cast ((boundedFlatCoefficientFullOpenBassTelescopeInclusion f 0).app a) κ)
    (boundedFlatCoefficientSectionPerfectKStableEquiv (op P, a) (n + 1) (Additive.ofMul x))
  exact (congrArg (boundedFlatCoefficientFineLocalizationConnecting f a (n : ℤ)) hc.symm).trans
    (boundedFlatCoefficientFineConnecting_perfect_sign f a n κ x)

end Quillen.PerfectComplexes
