/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientNegativeLocalizationBoundary
public import Quillen.Topology.Prespectrum.FiberLiftConnecting

/-!
# The original fine boundary through its specified fiber lift

The existing signed cone boundary equals the intrinsic connecting map of
the same whole-null fiber lift. The proof uses the original cone-to-fiber
connecting equation, without choosing a sign or a new null.
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

/-- The original fine boundary recovers the signed fiber boundary through the same null lift. -/
@[reassoc]
theorem boundedFlatCoefficientFineLocalizationConnecting_comp_fiberMap
    (a : Under R) (d : ℤ) :
    boundedFlatCoefficientFineLocalizationConnecting f a d ≫
        (stableHomotopyFunctor d).map
          (boundedFlatCoefficientSupportedBassTelescopeFullOpenFiberMap f a) =
      stableFiberConnecting ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a) d := by
  let c := (stableHomotopyFunctor (d + 1)).map
    ((boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap f).app a)
  let : IsIso c :=
    boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap_isStableEquivalence f a (d + 1)
  unfold boundedFlatCoefficientFineLocalizationConnecting
  rw [Category.assoc,
    ← boundedFlatCoefficientSupportedBassTelescopeFullOpenConeMap_connecting]
  exact IsIso.inv_hom_id_assoc c _

/-- The old cone-defined boundary is precisely the intrinsic boundary of its original lift. -/
theorem boundedFlatCoefficientFineLocalizationConnecting_eq_fiberLift
    (a : Under R) (d : ℤ) :
    letI : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
        ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
        ((boundedFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a))) :=
      boundedFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_isStableEquivalence f a d
    boundedFlatCoefficientFineLocalizationConnecting f a d =
      stableFiberLiftConnecting
        ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
        ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
        ((boundedFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a) d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((boundedFlatCoefficientAmbientBassTelescopeFullOpen f).app a)
        ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a)
        ((boundedFlatCoefficientSupportedBassTelescopeFullOpenNull f).homotopy a))) :=
      boundedFlatCoefficientSupportedBassTelescopeFullOpenFiberMap_isStableEquivalence f a d
  apply stableFiberLiftConnecting_unique
  exact boundedFlatCoefficientFineLocalizationConnecting_comp_fiberMap f a d

end Quillen.PerfectComplexes

