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
namespace QuillenTest.AuxiliaryFinePerfectConnecting
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

/-- The original supported K1 boundary retains the literal supported K0 endpoint and sign. -/
theorem auxiliary_Kone_boundary_original_supported_Kzero
    (a : Under R)
    (x : PerfectSupportedK (boundedFlatCoefficientOpenSupportOpen f T a).ι (0 + 1)) :
    let : CompactSpace (space (op P, a)) := compactSpace_space (op P, a)
    let : CompactSpace (space (op Q, a)) := compactSpace_space (op Q, a)
    let : QuasiSeparatedSpace (space (op Q, a)) := quasiSeparatedSpace_space (op Q, a)
    boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a ((0 : ℕ) : ℤ)
        (eqToHom (congrArg (stableHomotopyGroup
          ((boundedFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T).obj a))
          (show ((0 + 1 : ℕ) : ℤ) = ((0 : ℕ) : ℤ) + 1 from rfl))
          ((stableHomotopyFunctor ((0 + 1 : ℕ) : ℤ)).map
            ((boundedFlatCoefficientSupportedFullOpenBassTelescopeInclusion f T 0).app a)
            (auxiliaryOpenPerfectStableEquiv f T a (0 + 1)
              (Additive.ofMul x)))) =
      -((stableHomotopyFunctor ((0 : ℕ) : ℤ)).map
        ((boundedFlatCoefficientSupportedFiberBassTelescopeInclusion f T 0).app a)
        (auxiliaryFiberPerfectStableEquiv f T a 0
          (Additive.ofMul (qcqsPerfectSupportedConnectingHom (schemeMap f a)
            (boundedFlatCoefficientSupportOpen Q T a)
            (isCompact_iff_compactSpace.mpr
              (boundedFlatCoefficientSupportOpen_compactSpace Q T a)) 0 x)))) := by
  exact boundedFlatCoefficientAuxiliaryFineConnecting_perfectClass_sign f T a 0 rfl x

end QuillenTest.AuxiliaryFinePerfectConnecting
