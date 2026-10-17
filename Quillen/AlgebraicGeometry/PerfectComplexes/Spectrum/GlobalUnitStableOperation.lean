/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.GlobalUnitComponents


public import Quillen.AlgebraicGeometry.PerfectComplexes.GlobalUnitKOneInversion
public import Quillen.AlgebraicGeometry.PerfectComplexes.Spectrum.GlobalUnit
public import Quillen.Waldhausen.SConstruction.Iterated.ExactSelfTrackStableOperation

/-! # Inverse global units on the original flat-pullback stable operations -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes

/-- The actual inverse-unit track negates the original operation in every integer degree. -/
theorem perfectFlatUnitHomotopy_stableOperation_inv {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] (q : (Γ(X, ⊤))ˣ) (d : ℤ) :
    (perfectFlatUnitHomotopy f q⁻¹).stableOperation d =
      -(perfectFlatUnitHomotopy f q).stableOperation d := by
  unfold perfectFlatUnitHomotopy
  rw [perfectFlatPullbackUnitIso_inv]
  exact exactIsoSelfTrack_stableOperation_symm _ _
    (perfectFlatPullback_waldhausenExact f) (perfectFlatPullbackUnitIso f q) d

end Quillen.PerfectComplexes
