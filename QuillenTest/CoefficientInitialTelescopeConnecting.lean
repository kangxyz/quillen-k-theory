/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientInitialTelescopeConnecting

/-!
# Initial localization classes through the original finite full-open restriction

The fine boundary of an initial class can be computed by first applying the
literal finite coarse-to-full-open restriction and then its original stage-zero
inclusion. It agrees with the original supported inclusion of the intrinsic
initial boundary, in every signed degree.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PerfectComplexes

universe u

namespace QuillenTest.CoefficientInitialTelescopeConnecting

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The literal finite restriction route preserves the signed initial boundary class. -/
theorem fineBoundary_finiteRestriction (a : Under R) (d : ℤ)
    (x : stableHomotopyGroup ((boundedFlatCoefficientOpenBassDiagram f 0).obj a) (d + 1)) :
    let := boundedFlatCoefficientInitialFiberLift_isStableEquivalence f a d
    boundedFlatCoefficientFineLocalizationConnecting f a d
        ((stableHomotopyFunctor (d + 1)).map
          ((boundedFlatCoefficientFullOpenBassTelescopeInclusion f 0).app a)
          ((stableHomotopyFunctor (d + 1)).map
            ((boundedFlatCoefficientOpenBassRestriction f 0).app a) x)) =
      (stableHomotopyFunctor d).map
        ((boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a)
        (stableFiberLiftConnecting
          ((boundedFlatCoefficientSupportedForgetPrespectrumTransformation f).app a)
          ((boundedFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
          ((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a) d x) := by
  let := boundedFlatCoefficientInitialFiberLift_isStableEquivalence f a d
  have h := ConcreteCategory.congr_hom
    (boundedFlatCoefficientInitialConnecting_telescope f a d) x
  have ho := congrArg (stableHomotopyFunctor (d + 1)).map
    (NatTrans.congr_app (boundedFlatCoefficientOpenBassTelescopeInclusion_restriction f 0) a)
  have hs := ho.trans ((stableHomotopyFunctor (d + 1)).map_comp
    ((boundedFlatCoefficientOpenBassRestriction f 0).app a)
    ((boundedFlatCoefficientFullOpenBassTelescopeInclusion f 0).app a))
  exact (congrArg (boundedFlatCoefficientFineLocalizationConnecting f a d)
    (ConcreteCategory.congr_hom hs x)).symm.trans h.symm

end QuillenTest.CoefficientInitialTelescopeConnecting
