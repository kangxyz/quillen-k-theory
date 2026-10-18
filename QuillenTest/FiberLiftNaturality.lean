/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

import Quillen.Topology.Prespectrum.FiberLiftNaturality
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionFullOpenFiber

/-! # Same-null transport applied to the original global full-open fiber comparison -/
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.PerfectComplexes
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
universe u
variable {R : CommRingCat.{u}} {P Q : Over (Spec R)} (f : P ⟶ Q)
    [IsOpenImmersion f.left] (a : Under R)

-- The generic equality applies to the original whole null and all three original maps.
example :
    FullOpenTelescope.fiberMap f a ≫
        homotopyFiberMap (FullOpenTelescope.fiberSquare f a) =
      (SupportedTelescope.telescopeRestriction f).app a ≫
        homotopyFiberLift ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
          ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
          ((boundedFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a) := by
  exact homotopyFiberLift_naturality
    ((LocalizationTelescope.forget f).app a) ((FullOpenTelescope.openMap f).app a)
    ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
    ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
    ((FullOpenTelescope.null f).homotopy a)
    ((boundedFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a)
    ((SupportedTelescope.telescopeRestriction f).app a)
    ((telescopeRestriction Q).app a) ((telescopeRestriction P).app a)
    (congrArg (fun η => η.app a) (LocalizationTelescope.forget_square f)).symm
    (congrArg (fun η => η.app a) (FullOpenTelescope.openMap_square f)).symm
    (FullOpenTelescope.null_restriction f a)

-- The same actual comparison transports stability in both directions without compactness.
-- Compactness is needed to supply localization, not to transport this specified fiber lift.
example :
    IsStableEquivalence (FullOpenTelescope.fiberMap f a) ↔
      IsStableEquivalence
        (homotopyFiberLift ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
          ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
          ((boundedFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a)) := by
  exact homotopyFiberLift_isStableEquivalence_iff
    ((LocalizationTelescope.forget f).app a) ((FullOpenTelescope.openMap f).app a)
    ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
    ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
    ((FullOpenTelescope.null f).homotopy a)
    ((boundedFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a)
    ((SupportedTelescope.telescopeRestriction f).app a)
    ((telescopeRestriction Q).app a) ((telescopeRestriction P).app a)
    (congrArg (fun η => η.app a) (LocalizationTelescope.forget_square f)).symm
    (congrArg (fun η => η.app a) (FullOpenTelescope.openMap_square f)).symm
    (FullOpenTelescope.null_restriction f a)
    (SupportedTelescope.telescopeRestriction_isStableEquivalence f a)
    (telescopeRestriction_isStableEquivalence Q a)
    (telescopeRestriction_isStableEquivalence P a)

#print axioms homotopyFiberLift_naturality
#print axioms homotopyFiberLift_isStableEquivalence_iff
