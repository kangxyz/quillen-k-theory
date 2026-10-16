/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.GlobalUnit


public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.BoundedFlatPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnit

/-! Actual global-unit automorphisms and their original bounded-flat prespectrum tracks. -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The actual unit gives a full coherent self-homotopy of the original raw pullback map. -/
def boundedFlatPerfectUnitHomotopy {X Y : Scheme.{u}} (f : X ⟶ Y)
    (r : (Γ(X, ⊤))ˣ) :
    LoopPrespectrum.Homotopy (boundedFlatPerfectPrespectrumMap f)
      (boundedFlatPerfectPrespectrumMap f) :=
  exactOriginalPrespectrumIsoHomotopy _ _ (boundedFlatPerfectPullback_exact f)
    (boundedFlatPerfectPullback_exact f) (boundedFlatPerfectPullbackUnitIso f r)

end Quillen.PerfectComplexes
