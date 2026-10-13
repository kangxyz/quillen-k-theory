/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyCofiber.ReducedMappingConeSeparation
public import Quillen.Topology.Prespectrum.MappingCone
public import Quillen.Topology.Prespectrum.ParameterLooping
public import Quillen.Topology.Path.Separation

/-! # T1 separation of actual cone and parameter-looping levels -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum

/-- The actual based cone inherits T1 separation from both input levels. -/
instance mappingConeSpaceT1Space {E F : LoopPrespectrum.{u}} (f : E ⟶ F) (n : ℕ)
    [T1Space (E.space n)] [T1Space (F.space n)] : T1Space ((mappingCone f).space n) :=
  ReducedMappingCone.space_t1Space (E.point n) (F.point n) (f.map n) (f.map_point n)

/-- Actual parameter-correct looping preserves T1 separation at every level. -/
instance parameterLoopingSpaceT1Space (E : LoopPrespectrum.{u}) (n : ℕ)
    [T1Space (E.space n)] : T1Space ((parameterLooping E).space n) := by
  change T1Space (Path (E.point n) (E.point n))
  infer_instance

end Quillen.LoopPrespectrum
