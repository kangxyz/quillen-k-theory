/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassFineTelescopeComparison

/-!
# Original connective coefficient K-groups in the fine Bass telescope

The original normalized-evaluation comparison followed by the actual stage-zero inclusion
identifies every original connective K-group with the same fine completion. This is a
coefficient-natural isomorphism for a compact quasi-separated base scheme, and the displayed
component formula retains both original maps.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]
variable [QuasiSeparatedSpace P.left]

/-- The actual initial-stage inclusion is naturally invertible in every connective degree. -/
instance boundedFlatCoefficientAmbientBassTelescopeConnectiveInclusion_isIso (n : ℕ) :
    IsIso (Functor.whiskerRight (boundedFlatCoefficientAmbientBassTelescopeInclusion P 0)
      (stableHomotopyFunctor (n : ℤ))) := by
  let : ∀ a, IsIso ((Functor.whiskerRight
      (boundedFlatCoefficientAmbientBassTelescopeInclusion P 0)
      (stableHomotopyFunctor (n : ℤ))).app a) := fun a =>
    boundedFlatCoefficientAmbientBassTelescopeInclusion_isIso_of_le P 0 a (n : ℤ) (by omega)
  exact NatIso.isIso_of_isIso_app _

/-- Original connective K-groups identify naturally with the actual fine Bass completion. -/
def boundedFlatCoefficientAmbientKTelescopeComparison (n : ℕ) :
    boundedFlatCoefficientKAddFunctor P n ≅
      boundedFlatCoefficientAmbientBassTelescopeFunctor P ⋙ stableHomotopyFunctor (n : ℤ) :=
  boundedFlatCoefficientSectionKStableNatIso P n ≪≫
    asIso (Functor.whiskerRight (boundedFlatCoefficientAmbientBassTelescopeInclusion P 0)
      (stableHomotopyFunctor (n : ℤ)))

/-- Every original K-element uses the normalized-evaluation comparison and unchanged inclusion.
-/
theorem boundedFlatCoefficientAmbientKTelescopeComparison_hom_app (n : ℕ) (a : Under R) :
    (boundedFlatCoefficientAmbientKTelescopeComparison P n).hom.app a =
      (boundedFlatCoefficientSectionKStableNatIso P n).hom.app a ≫
        (stableHomotopyFunctor (n : ℤ)).map
          ((boundedFlatCoefficientAmbientBassTelescopeInclusion P 0).app a) := rfl

end Quillen.PerfectComplexes
