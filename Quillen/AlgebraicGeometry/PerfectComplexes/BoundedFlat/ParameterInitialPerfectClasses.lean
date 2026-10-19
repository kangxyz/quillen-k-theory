/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterInitialModelClasses

/-! # The original supported perfect K comparison on independent current initial classes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.LoopPrespectrum Quillen.KTheory.Bass Quillen.Waldhausen.IteratedS
open Quillen.KTheory.Bass.SchemeNaturalSeed
universe u
namespace Quillen.PerfectComplexes.ParameterFullCurrentNull
open GlobalSectionChangeIndex ParameterLaurentTrack
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace Q.left]

/-- Original supported perfect K classes use the existing evaluation comparison in every degree. -/
theorem current_fine_originalSupportedClass
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : ((ParameterModels.supported f.left).obj (specUnder.obj a)).waldhausen.K n) :
    (currentFineSupportComparison f a (n : ℤ)).hom
        (currentModelClass (ParameterModels.supported f.left) (supportedTrack f.left)
          (specUnder.obj a) n x) =
      (stableHomotopyFunctor (n : ℤ)).map
        ((boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a)
        (boundedFlatCoefficientSupportedKStableEquiv f a n
          (Additive.ofMul (boundedFlatCoefficientSupportedPerfectKEquiv f a n
            (Quillen.Waldhausen.KMap
              (((parameterSupportedRowIso f).hom ≫ supportedRowRestriction f).app a).exact
              n x)))) := by
  rw [boundedFlatCoefficientSupportedKStableEquiv_evaluation]
  exact current_fine_fiber_modelClass f a n x

/-- Degree zero is the unchanged original map used by the supported negative recursion. -/
theorem current_fine_originalSupportedZeroClass
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (x : ((ParameterModels.supported f.left).obj (specUnder.obj a)).waldhausen.K 0) :
    (currentFineSupportComparison f a 0).hom
        (currentModelClass (ParameterModels.supported f.left) (supportedTrack f.left)
          (specUnder.obj a) 0 x) =
      (stableHomotopyFunctor 0).map
        ((boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a)
        ((boundedFlatCoefficientSupportedBassBottomZeroIso f a).hom
          (Additive.ofMul (boundedFlatCoefficientSupportedPerfectKEquiv f a 0
            (Quillen.Waldhausen.KMap
              (((parameterSupportedRowIso f).hom ≫ supportedRowRestriction f).app a).exact
              0 x)))) :=
  current_fine_originalSupportedClass f a 0 x

end Quillen.PerfectComplexes.ParameterFullCurrentNull
