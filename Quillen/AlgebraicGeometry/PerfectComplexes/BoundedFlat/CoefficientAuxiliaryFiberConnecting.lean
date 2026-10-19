/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedFullOpenBassLocalization
public import Quillen.Topology.Prespectrum.FiberLiftConnecting

/-!
# The original auxiliary-supported cone boundary through its specified fiber lift

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
  [QuasiSeparatedSpace Q.left] (T : Q.left.Opens) [CompactSpace T]

/-- The signed cone boundary of the original G7 auxiliary-supported full-open diagram. -/
def boundedFlatCoefficientAuxiliaryLocalizationConnecting (a : Under R) (d : ℤ) :
    stableHomotopyGroup
        ((boundedFlatCoefficientSupportedFullOpenBassTelescopeFunctor f T).obj a) (d + 1) ⟶
      stableHomotopyGroup
        ((boundedFlatCoefficientSupportedFiberBassTelescopeFunctor f T).obj a) d :=
  let := boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_isStableEquivalence
    f T a (d + 1)
  inv ((stableHomotopyFunctor (d + 1)).map
    ((boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a)) ≫
      stableMappingConeConnecting
        ((boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
        (boundedFlatCoefficientSupportedFiberBassTelescopeForget_coneFiber_isStableEquivalence
          f T a) d

/-- The original fine boundary recovers the signed fiber boundary through the same null lift. -/
@[reassoc]
theorem boundedFlatCoefficientAuxiliaryLocalizationConnecting_comp_fiberMap
    (a : Under R) (d : ℤ) :
    boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a d ≫
        (stableHomotopyFunctor d).map
          (boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap f T a) =
      stableFiberConnecting
        ((boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a) d := by
  let c := (stableHomotopyFunctor (d + 1)).map
    ((boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap f T).app a)
  let : IsIso c :=
    boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_isStableEquivalence
      f T a (d + 1)
  unfold boundedFlatCoefficientAuxiliaryLocalizationConnecting
  rw [Category.assoc,
    ← boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenConeMap_connecting]
  exact IsIso.inv_hom_id_assoc c _

/-- The old cone-defined boundary is precisely the intrinsic boundary of its original lift. -/
theorem boundedFlatCoefficientAuxiliaryLocalizationConnecting_eq_fiberLift
    (a : Under R) (d : ℤ) :
    letI : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a)
        ((boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
        ((boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a))) :=
      boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_isStableEquivalence f T a d
    boundedFlatCoefficientAuxiliaryLocalizationConnecting f T a d =
      stableFiberLiftConnecting
        ((boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
        ((boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a)
        ((boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a) d := by
  let : IsIso ((stableHomotopyFunctor d).map
      (homotopyFiberLift ((boundedFlatCoefficientSupportedAmbientBassTelescopeFullOpen f T).app a)
        ((boundedFlatCoefficientSupportedFiberBassTelescopeForget f T).app a)
        ((boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a))) :=
      boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenFiberMap_isStableEquivalence f T a d
  apply stableFiberLiftConnecting_unique
  exact boundedFlatCoefficientAuxiliaryLocalizationConnecting_comp_fiberMap f T a d

end Quillen.PerfectComplexes

