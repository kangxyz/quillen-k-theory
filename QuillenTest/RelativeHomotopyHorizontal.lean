/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.HomotopyTransport
public import Quillen.Topology.Prespectrum.RelativeHomotopyHorizontal

/-! Consumers separate comparison time, path time, and original structure time. -/
@[expose] public section
noncomputable section
open CategoryTheory Quillen.LoopPrespectrum
universe u
namespace QuillenTest.RelativeHomotopyHorizontal

open Quillen
variable {E F : Quillen.LoopPrespectrum.{u}} {f g h f' g' : E ⟶ F}
  {H H' : Homotopy f g} {K K' : Homotopy g h}

/-- Reversal acts only on the original path coordinate. -/
theorem original_path_reversal (J : H.RelHomotopy H') (n : ℕ)
    (r s : unitInterval) (x : E.space n) :
    J.symmPath.level n (r, (s, x)) = J.level n (r, (unitInterval.symm s, x)) := rfl

/-- Concatenation preserves the independent original structure parameter. -/
theorem independent_structure_time (J : H.RelHomotopy H') (L : K.RelHomotopy K')
    (n : ℕ) (r s t : unitInterval) (x : E.space n) :
    (J.hcomp L).level (n+1) (r, (s, E.structureMap n x t)) =
      F.structureMap n ((J.hcomp L).level n (r, (s, x))) t :=
  (J.hcomp L).comm n r s x t

/-- Endpoint-arrow transport changes no actual continuous square coordinate. -/
theorem unchanged_transport (J : H.RelHomotopy H') (hf : f = f') (hg : g = g')
    (n : ℕ) (r s : unitInterval) (x : E.space n) :
    (J.cast hf hg).level n (r, (s, x)) = J.level n (r, (s, x)) := rfl

end QuillenTest.RelativeHomotopyHorizontal
