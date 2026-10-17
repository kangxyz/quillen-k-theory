/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedFineTelescopeComparison

/-!
# Original connective supported coefficient K-groups in the fine Bass telescope

The original supported evaluation comparison followed by the actual stage-zero inclusion
identifies every original connective supported K-group with the same fine completion. This is a
coefficient-natural isomorphism for a qcqs ambient scheme with compact removed open. The
displayed component formula retains both original maps.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The actual initial-stage inclusion is naturally invertible in every connective degree. -/
instance boundedFlatCoefficientSupportedBassTelescopeConnectiveInclusion_isIso (n : ℕ) :
    IsIso (Functor.whiskerRight (boundedFlatCoefficientSupportedBassTelescopeInclusion f 0)
      (stableHomotopyFunctor (n : ℤ))) := by
  let : ∀ a, IsIso ((Functor.whiskerRight
      (boundedFlatCoefficientSupportedBassTelescopeInclusion f 0)
      (stableHomotopyFunctor (n : ℤ))).app a) := fun a =>
    boundedFlatCoefficientSupportedBassTelescopeInclusion_isIso_of_le f 0 a (n : ℤ) (by omega)
  exact NatIso.isIso_of_isIso_app _

/-- Original connective K-groups identify naturally with the actual fine Bass completion. -/
def boundedFlatCoefficientSupportedKTelescopeComparison (n : ℕ) :
    (boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedKAddFunctor n) ≅
      boundedFlatCoefficientSupportedBassTelescopeFunctor f ⋙ stableHomotopyFunctor (n : ℤ) :=
  boundedFlatCoefficientSupportedKStableNatIso f n ≪≫
    asIso (Functor.whiskerRight (boundedFlatCoefficientSupportedBassTelescopeInclusion f 0)
      (stableHomotopyFunctor (n : ℤ)))

/-- Every original K-element uses the original supported evaluation and unchanged inclusion.
-/
theorem boundedFlatCoefficientSupportedKTelescopeComparison_hom_app (n : ℕ) (a : Under R) :
    (boundedFlatCoefficientSupportedKTelescopeComparison f n).hom.app a =
      (boundedFlatCoefficientSupportedKStableNatIso f n).hom.app a ≫
        (stableHomotopyFunctor (n : ℤ)).map
          ((boundedFlatCoefficientSupportedBassTelescopeInclusion f 0).app a) := rfl

/-- The connective and negative constructions use the identical original degree-zero map. -/
theorem boundedFlatCoefficientSupportedKTelescopeComparison_zero_hom_app (a : Under R) :
    (boundedFlatCoefficientSupportedKTelescopeComparison f 0).hom.app a =
      (boundedFlatCoefficientSupportedNegativeKTelescopeComparison f 0).hom.app a := rfl

end Quillen.PerfectComplexes
