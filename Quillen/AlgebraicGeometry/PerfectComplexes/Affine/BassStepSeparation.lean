/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassStep
public import Quillen.Topology.Prespectrum.HomotopyPushoutSeparation
public import Quillen.Topology.Prespectrum.ConeLoopSeparation
public import Quillen.Waldhausen.SConstruction.Iterated.Separation

/-! # T1 separation of the original affine Bass-step levels

The actual two polynomial cylinders, original square cone and parameter-correct looping
all retain T1 separation. No comparison with a negative K-group is used.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- Every original affine Bass-step level is T1 over an arbitrary base ring. -/
instance affineBassStepSpaceT1Space (R : CommRingCat.{u}) (n : ℕ) :
    T1Space ((affineBassStep R).space n) := by
  unfold affineBassStep
  infer_instance

end Quillen.PerfectComplexes
