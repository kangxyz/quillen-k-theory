/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterTelescopeNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedParameterTelescopeForget
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterFineRestrictionSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalParameterIteratedOpenIdentification
public import Quillen.Topology.Prespectrum.FiberLiftNaturality

/-!
# The original parameter seed-iterate full-open fiber lift is stable

The three actual Spec-row comparisons preserve support forgetting, full-open
restriction, and the entire originally selected null. The existing fine
localization theorem therefore transports to the original parameter
seed-iterate lift. This theorem concerns that actual iterated-seed model.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.LoopPrespectrum
universe u
namespace Quillen.PerfectComplexes.ParameterFullCurrentNull
open GlobalSectionChangeIndex GlobalParameterCoefficient
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left]

/-- The actual original full-open parameter map agrees through the two fine comparisons. -/
theorem iteratedOpen_fine_square :
    Functor.whiskerLeft specUnder (iteratedOpen f.left) ≫ fineTelescopeComparison P =
      fineTelescopeComparison Q ≫ boundedFlatCoefficientAmbientBassTelescopeFullOpen f := by
  have h := fine_fullRestriction_square f
  rw [parameterTelescopeRestriction_eq_iteratedOpen] at h
  exact h

variable [CompactSpace P.left] [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]

/-- At every integral Spec-row coefficient, the original same-null iterated-seed lift is stable. -/
theorem iteratedLift_spec_isStableEquivalence
    (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    IsStableEquivalence (iteratedLift f.left (specUnder.obj a)) := by
  have hf := congrArg (fun k => k.app a)
    (GlobalSupportedParameterCoefficient.fineTelescope_forget_square f)
  have hr := congrArg (fun k => k.app a) (iteratedOpen_fine_square f)
  have hiff := homotopyFiberLift_isStableEquivalence_iff
    ((iteratedForget f.left).app (specUnder.obj a))
    ((iteratedOpen f.left).app (specUnder.obj a))
    ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
    ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
    ((iteratedNull f.left).homotopy (specUnder.obj a))
    ((boundedFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a)
    ((GlobalSupportedParameterCoefficient.fineTelescopeComparison f).app a)
    ((fineTelescopeComparison Q).app a) ((fineTelescopeComparison P).app a)
    hf hr.symm (telescope_fullNull_fine_square f a)
    (GlobalSupportedParameterCoefficient.fineTelescopeComparison_stable f a)
    (fineTelescopeComparison_stable Q a) (fineTelescopeComparison_stable P a)
  exact hiff.mpr
    (boundedFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_isStableEquivalence f a)

end Quillen.PerfectComplexes.ParameterFullCurrentNull
