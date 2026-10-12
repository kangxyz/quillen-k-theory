/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.ConeParameterLoopingExcision
public import Quillen.Waldhausen.SConstruction.Iterated.FiniteConnectivity
public import Quillen.Waldhausen.SConstruction.Iterated.PointHEP

/-!
# Loop-cofiber comparison for actual iterated-S models

Every original morphism between the actual model prespectra has stable loop-cofiber
comparison. The genuine original S-level growth, all-point coverage, T1 topology, and literal
chosen-point HEP discharge both excision inputs, including the looped chosen point.
-/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
universe u
namespace Quillen.Waldhausen.IteratedS
variable {W V : Model.{u}} (f : prespectrum W ⟶ prespectrum V)

/-- Every original map between actual models has genuine stable excision after parameter looping.
-/
theorem parameterLoopingMap_coneFiber_isStableEquivalence :
    IsStableEquivalence (mappingConeFiberComparison (parameterLoopingMap f)) :=
  parameterLoopingMap_coneFiber_isStableEquivalence_of_linearGrowth f 0
    (prespectrum_point_homotopyExtensionProperty W)
    (prespectrum_point_homotopyExtensionProperty V)
    (fun n x k hk ↦ prespectrum_positiveLevel_homotopyGroup_subsingleton_at W (n + 1) k
      (by omega) x)
    (fun n x k hk ↦ prespectrum_positiveLevel_homotopyGroup_subsingleton_at V (n + 1) k
      (by omega) x)

/-- The unchanged original loop-cofiber comparison is stable with no additional model premises. -/
theorem mappingConeParameterLoopingComparison_isStableEquivalence :
    IsStableEquivalence (mappingConeParameterLoopingComparison f) :=
  mappingConeParameterLoopingComparison_isStableEquivalence_of_linearGrowth f 0
    (prespectrum_point_homotopyExtensionProperty W)
    (prespectrum_point_homotopyExtensionProperty V)
    (fun n x k hk ↦ prespectrum_positiveLevel_homotopyGroup_subsingleton_at W (n + 1) k
      (by omega) x)
    (fun n x k hk ↦ prespectrum_positiveLevel_homotopyGroup_subsingleton_at V (n + 1) k
      (by omega) x)

end Quillen.Waldhausen.IteratedS
