/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassFineRangeInvertibility
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedBassTelescope
public import Quillen.Topology.Prespectrum.TelescopeStableInclusion

/-!
# Original coefficient groups in the actual fine Bass telescope

Every original stage inclusion is invertible in its proved finite-stage degree range.
Composing that actual inclusion with the original finite-bottom comparison identifies the
scheme Bass negative groups, including degree zero, with this same fine telescope. The
comparison is natural on the full coefficient category and retains the original quotient maps.
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
variable {R : CommRingCat.{u}} (P : Over (Spec R)) [CompactSpace P.left]
variable [QuasiSeparatedSpace P.left]

/-- The unchanged finite-stage inclusion is invertible throughout the actual stable range. -/
theorem boundedFlatCoefficientAmbientBassTelescopeInclusion_isIso_of_le
    (i : ℕ) (a : Under R) (d : ℤ) (hd : -(i : ℤ) ≤ d) :
    IsIso ((stableHomotopyFunctor d).map
      ((boundedFlatCoefficientAmbientBassTelescopeInclusion P i).app a)) := by
  let : ∀ j k, T1Space (((boundedFlatCoefficientAmbientBassDiagram P j).obj a).space k) :=
    fun j k => modelDiagramIterateSpaceT1Space (laurentUnderSquareFunctor R) j
      (boundedFlatCoefficientSectionModelRow P) a k
  exact Telescope.inclusion_stableMap_isIso_of_tail
    (fun j => (boundedFlatCoefficientAmbientBassDiagram P j).obj a)
    (fun j => (boundedFlatCoefficientAmbientBassTransition P j).app a) d i
    (fun j hj => boundedFlatCoefficientAmbientBassTransition_isIso_of_le P j a d (by omega))

/-- At the original bottom degree the actual inclusion is an isomorphism of coefficient functors.
-/
instance boundedFlatCoefficientAmbientBassTelescopeBottomInclusion_isIso (i : ℕ) :
    IsIso (Functor.whiskerRight (boundedFlatCoefficientAmbientBassTelescopeInclusion P i)
      (stableHomotopyFunctor (-(i : ℤ)))) := by
  let : ∀ a, IsIso ((Functor.whiskerRight (boundedFlatCoefficientAmbientBassTelescopeInclusion P i)
      (stableHomotopyFunctor (-(i : ℤ)))).app a) := fun a =>
    boundedFlatCoefficientAmbientBassTelescopeInclusion_isIso_of_le P i a (-(i : ℤ)) le_rfl
  exact NatIso.isIso_of_isIso_app _

/-- The original scheme negative groups are naturally the groups of the actual fine completion.
-/
def boundedFlatCoefficientAmbientNegativeKTelescopeComparison (i : ℕ) :
    boundedFlatCoefficientQuasiCompactRow P ⋙ Bass.negativeKFunctor i ≅
      boundedFlatCoefficientAmbientBassTelescopeFunctor P ⋙ stableHomotopyFunctor (-(i : ℤ)) :=
  boundedFlatCoefficientAmbientNegativeKComparison P i ≪≫
    asIso (Functor.whiskerRight (boundedFlatCoefficientAmbientBassTelescopeInclusion P i)
      (stableHomotopyFunctor (-(i : ℤ))))

/-- The comparison is the original finite-bottom map followed by the actual stage inclusion. -/
theorem boundedFlatCoefficientAmbientNegativeKTelescopeComparison_hom_app
    (i : ℕ) (a : Under R) :
    (boundedFlatCoefficientAmbientNegativeKTelescopeComparison P i).hom.app a =
      (boundedFlatCoefficientAmbientNegativeKComparison P i).hom.app a ≫
        (stableHomotopyFunctor (-(i : ℤ))).map
          ((boundedFlatCoefficientAmbientBassTelescopeInclusion P i).app a) := rfl

/-- The original Laurent quotient is retained after passage to the actual fine completion. -/
@[reassoc]
theorem boundedFlatCoefficientAmbientNegativeKTelescopeComparison_π (i : ℕ) (a : Under R) :
    (Bass.negativeKFunctor i).map ((boundedFlatCoefficientLaurentIso P).hom.app a) ≫
      Bass.negativeKπ ((boundedFlatCoefficientQuasiCompactRow P).obj a).unop i ≫
        (boundedFlatCoefficientAmbientNegativeKTelescopeComparison P (i + 1)).hom.app a =
    (boundedFlatCoefficientAmbientNegativeKComparison P i).hom.app
        ((laurentUnderFunctor R).obj a) ≫
      (Quillen.Bass.TwoChart.contractionπ (underToLaurent R) (underToLaurentInvert R)
        (boundedFlatCoefficientAmbientBassDiagram P i ⋙
          stableHomotopyFunctor (-(i : ℤ)))).app a ≫
        (boundedFlatCoefficientAmbientBassBottomContractionIso P i).hom.app a ≫
          (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
            ((boundedFlatCoefficientAmbientBassTelescopeInclusion P (i + 1)).app a) := by
  rw [boundedFlatCoefficientAmbientNegativeKTelescopeComparison_hom_app]
  simpa only [Category.assoc] using
    (boundedFlatCoefficientAmbientNegativeKComparison_π P i a) =≫
      (stableHomotopyFunctor (-((i + 1 : ℕ) : ℤ))).map
        ((boundedFlatCoefficientAmbientBassTelescopeInclusion P (i + 1)).app a)

end Quillen.PerfectComplexes
