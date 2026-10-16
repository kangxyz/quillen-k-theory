/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Morphisms.OpenImmersion.Pair.AffineBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Compactness of the original affine open fibers

Compactness of the original open makes its map to the affine base quasi-compact.
Base change therefore gives compactness of each actual fixed pullback open.
No flatness hypothesis is imposed on the coefficient arrow.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.AffineOpenPair

/-- Every original fixed pullback open is compact when the initial open is compact. -/
theorem compactSpace_openSpace {R : CommRingCat.{u}} {U : AlgebraicGeometry.Scheme.{u}}
    (j : U ⟶ Spec R) [CompactSpace U] (a : Under R) : CompactSpace (openSpace j a) := by
  let : QuasiCompact j := quasiCompact_of_compactSpace j
  exact inferInstanceAs
    (CompactSpace ((pullback j (Spec.map a.hom)) : AlgebraicGeometry.Scheme.{u}))

end AlgebraicGeometry.Scheme.AffineOpenPair
