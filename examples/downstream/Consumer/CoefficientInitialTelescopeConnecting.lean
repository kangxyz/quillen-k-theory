/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientInitialTelescopeConnecting

/-!
# Initial boundary kernels enter the actual fine boundary kernel

A client uses the original stage-zero coarse inclusion and unchanged telescope
restriction to send classes killed by the intrinsic initial boundary to classes
killed by the existing fine localization boundary.
-/
@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum Quillen.PerfectComplexes

universe u

namespace Consumer.CoefficientInitialTelescopeConnecting

variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The unchanged open inclusion and restriction carry the initial kernel into the fine kernel. -/
theorem initialBoundary_kernel_maps_to_fineBoundary_kernel (a : Under R) (d : ℤ)
    (x : stableHomotopyGroup ((boundedFlatCoefficientOpenBassDiagram f 0).obj a) (d + 1)) :
    let := boundedFlatCoefficientInitialFiberLift_isStableEquivalence f a d
    stableFiberLiftConnecting
        ((boundedFlatCoefficientSupportedForgetPrespectrumTransformation f).app a)
        ((boundedFlatCoefficientAmbientOpenPrespectrumTransformation f).app a)
        ((boundedFlatCoefficientSupportedOpenDiagramNull f).homotopy a) d x = 0 →
      boundedFlatCoefficientFineLocalizationConnecting f a d
        ((stableHomotopyFunctor (d + 1)).map
          ((boundedFlatCoefficientOpenBassTelescopeInclusion f 0).app a ≫
            (boundedFlatCoefficientOpenBassTelescopeRestriction f).app a) x) = 0 := by
  let := boundedFlatCoefficientInitialFiberLift_isStableEquivalence f a d
  dsimp only
  intro hx
  have h := ConcreteCategory.congr_hom
    (boundedFlatCoefficientInitialConnecting_telescope f a d) x
  exact h.symm.trans ((congrArg
    ((stableHomotopyFunctor d).map
      ((boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a)) hx).trans (map_zero _))

end Consumer.CoefficientInitialTelescopeConnecting
