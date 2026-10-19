/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientAuxiliaryFinePerfectConnecting

/-! The original inverse-open supported K1 class has its actual union-support K0 boundary. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.PerfectComplexes
open Quillen.Waldhausen Quillen.Waldhausen.Fibration Quillen.Waldhausen.IteratedS
open Quillen.LoopPrespectrum AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Consumer.AuxiliaryFinePerfectConnecting
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

/-- The intrinsic auxiliary boundary kills the original supported ambient restriction. -/
theorem auxiliary_boundary_kills_original_supported_restriction
    (a : Under R) (n : ℕ) (κ : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1)
    (x : PerfectSupportedK (boundedFlatCoefficientSupportOpen Q T a).ι (n + 1)) :
    let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
    let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
    let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
    boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a (n : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup
          ((boundedFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T).obj a)) κ)
          ((stableHomotopyFunctor ((n + 1 : ℕ) : ℤ)).map
            ((boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a)
            (auxiliaryOpenPerfectStableEquiv f T a (n + 1)
              (Additive.ofMul (perfectSupportedKRestrict (schemeMap f a)
                (boundedFlatCoefficientSupportOpen Q T a) (n + 1) x))))) = 0 := by
  let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
  let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
  let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
  let hT := isCompact_iff_compactSpace.mpr
    (boundedFlatCoefficientSupportOpen_compactSpace Q T a)
  have hδ : qcqsPerfectSupportedConnectingHom (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a) hT n
      (perfectSupportedKRestrict (schemeMap f a)
        (boundedFlatCoefficientSupportOpen Q T a) (n + 1) x) = 1 := by
    apply MonoidHom.mem_ker.mp
    rw [← range_qcqs_perfectSupportedKRestrict_eq_ker_qcqsPerfectSupportedConnectingHom]
    exact ⟨x, rfl⟩
  have hs := boundedFlatCoefficientAuxiliaryFineConnecting_perfectClass_sign f T a n κ
    (perfectSupportedKRestrict (schemeMap f a)
      (boundedFlatCoefficientSupportOpen Q T a) (n + 1) x)
  dsimp only at hs ⊢
  rw [hs, hδ]
  simp

end Consumer.AuxiliaryFinePerfectConnecting
