/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedFineRangeInvertibility
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedBassTelescope
public import Quillen.Topology.Prespectrum.TelescopeStableInclusion

/-!
# Original supported coefficient groups in the actual fine Bass telescope

Every original stage inclusion is invertible in its proved finite-stage degree range.
Composing that actual inclusion with the original finite-bottom comparison identifies the
supported pair Bass negative groups, including degree zero, with this same fine telescope. The
comparison is natural on the full coefficient category and retains the original quotient maps.
The ambient scheme is qcqs and the removed open is compact.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.KTheory.Bass
open CommRingCat.PolynomialLaurent
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

/-- The unchanged finite-stage inclusion is invertible throughout the actual stable range. -/
theorem boundedFlatCoefficientSupportedBassTelescopeInclusion_isIso_of_le
    (i : ℕ) (a : Under R) (d : ℤ) (hd : -(i : ℤ) ≤ d) :
    IsIso ((stableHomotopyFunctor d).map
      ((boundedFlatCoefficientSupportedBassTelescopeInclusion f i).app a)) := by
  let : ∀ j k, T1Space (((boundedFlatCoefficientSupportedBassDiagram f j).obj a).space k) :=
    fun j k => modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) j
      (boundedFlatCoefficientSupportedModelFunctor f) a k
  exact Telescope.inclusion_stableMap_isIso_of_tail
    (fun j => (boundedFlatCoefficientSupportedBassDiagram f j).obj a)
    (fun j => (boundedFlatCoefficientSupportedBassTransition f j).app a) d i
    (fun j hj => boundedFlatCoefficientSupportedBassTransition_isIso_of_le f j a d (by omega))

/-- At the original bottom degree the actual inclusion is an isomorphism of coefficient functors.
-/
instance boundedFlatCoefficientSupportedBassTelescopeBottomInclusion_isIso (i : ℕ) :
    IsIso (Functor.whiskerRight (boundedFlatCoefficientSupportedBassTelescopeInclusion f i)
      (stableHomotopyFunctor (-(i : ℤ)))) := by
  let : ∀ a, IsIso ((Functor.whiskerRight
      (boundedFlatCoefficientSupportedBassTelescopeInclusion f i)
      (stableHomotopyFunctor (-(i : ℤ)))).app a) := fun a =>
    boundedFlatCoefficientSupportedBassTelescopeInclusion_isIso_of_le f i a (-(i : ℤ)) le_rfl
  exact NatIso.isIso_of_isIso_app _

/-- The original supported negative groups are naturally the groups of the actual fine completion.
-/
def boundedFlatCoefficientSupportedNegativeKTelescopeComparison (i : ℕ) :
    boundedFlatCoefficientQuasiCompactOpenPairRow f ⋙ Bass.supportedNegativeKFunctor i ≅
      boundedFlatCoefficientSupportedBassTelescopeFunctor f ⋙ stableHomotopyFunctor (-(i : ℤ)) :=
  boundedFlatCoefficientSupportedNegativeKComparison f i ≪≫
    asIso (Functor.whiskerRight (boundedFlatCoefficientSupportedBassTelescopeInclusion f i)
      (stableHomotopyFunctor (-(i : ℤ))))

/-- The comparison is the original finite-bottom map followed by the actual stage inclusion. -/
theorem boundedFlatCoefficientSupportedNegativeKTelescopeComparison_hom_app
    (i : ℕ) (a : Under R) :
    (boundedFlatCoefficientSupportedNegativeKTelescopeComparison f i).hom.app a =
      (boundedFlatCoefficientSupportedNegativeKComparison f i).hom.app a ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((boundedFlatCoefficientSupportedBassTelescopeInclusion f i).app a) := rfl

/-- The original Laurent quotient is retained after passage to the actual fine completion. -/
@[reassoc]
theorem boundedFlatCoefficientSupportedNegativeKTelescopeComparison_π (i : ℕ) (a : Under R) :
    (Bass.supportedNegativeKFunctor i).map
      ((boundedFlatCoefficientSupportedLaurentIso f).hom.app a) ≫
      Bass.supportedNegativeKπ ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a).unop i ≫
        (boundedFlatCoefficientSupportedNegativeKTelescopeComparison f (i + 1)).hom.app a =
    (boundedFlatCoefficientSupportedNegativeKComparison f i).hom.app
        ((laurentUnderFunctor R).obj a) ≫
      (Quillen.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
        (boundedFlatCoefficientSupportedBassDiagram f i ⋙
          stableHomotopyFunctor (-(i : ℤ)))).app a ≫
        (boundedFlatCoefficientSupportedBassBottomContractionIso f i).hom.app a ≫
          (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
            ((boundedFlatCoefficientSupportedBassTelescopeInclusion f (i + 1)).app a) := by
  rw [boundedFlatCoefficientSupportedNegativeKTelescopeComparison_hom_app]
  simpa only [Category.assoc] using
    (boundedFlatCoefficientSupportedNegativeKComparison_π f i a) =≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedFlatCoefficientSupportedBassTelescopeInclusion f (i + 1)).app a)

end Quillen.PerfectComplexes
