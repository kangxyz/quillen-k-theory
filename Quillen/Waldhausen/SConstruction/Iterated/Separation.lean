/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.Prespectrum
public import Quillen.Topology.Path.Separation
public import Quillen.Topology.Realization.EdgePathPresentation.Skeleton

/-!
# Separation of the original iterated S-prespectrum

The actual simplicial realizations are T1. The degree-zero based-loop space
inherits T1 separation, so every original level of the iterated S-prespectrum
is T1, including the version using the proved small model.
-/
@[expose] public section

open CategoryTheory
universe u v
namespace Quillen.Waldhausen.IteratedS

instance stageSpaceT1Space (r : ℕ) (W : Model.{u}) : T1Space (stageSpace r W) := by
  unfold stageSpace
  infer_instance

instance prespectrumSpaceT1Space (W : Model.{u}) (n : ℕ) :
    T1Space ((prespectrum W).space n) := by
  cases n with
  | zero =>
    change T1Space (Path (stagePoint 0 W) (stagePoint 0 W))
    infer_instance
  | succ r =>
    change T1Space (stageSpace r W)
    infer_instance

instance originalPrespectrumSpaceT1Space {C : Type u} [Category.{v} C]
    (W : Structure C) (n : ℕ) : T1Space ((originalPrespectrum W).space n) :=
  prespectrumSpaceT1Space (modelOf W) n

end Quillen.Waldhausen.IteratedS
