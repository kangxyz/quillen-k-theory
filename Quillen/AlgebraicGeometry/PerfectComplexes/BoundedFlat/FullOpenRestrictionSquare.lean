/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.FullOpenRestrictionSquare


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.FullOpenPseudofunctor
public import Quillen.AlgebraicGeometry.PerfectComplexes.PairRestriction
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.GlobalUnitPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.OpenScalarUnit

/-!
# The original full-open restriction components and coefficient squares

Each component is actual bounded-flat pullback along the specified open inclusion. The
coefficient comparison is the preexisting open-pair pullback isomorphism, including its actual
scheme-square equality. Original restriction of the scalar is identified with the same target
unit, and original bounded-flat pullback retains that unit as well. These formulas do not
assert a full-open cofinality equivalence or identify independently chosen zeros.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

noncomputable section
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.AffineOpenPair
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} {U : Scheme.{u}} (j : U ⟶ Spec R) [IsOpenImmersion j]

/-- The original relative-open weak class makes precisely this component Waldhausen-exact. -/
theorem boundedFlatAffineFullOpenRestriction_exact (a : Under R) :
    Waldhausen.IsExact (boundedFlatPerfectOpenWaldhausen (inclusion j a)).cof
      (boundedFlatPerfectOpenWaldhausen (inclusion j a)).weq
      (boundedFlatPerfectWaldhausen (openSpace j a)).cof
      (boundedFlatPerfectWaldhausen (openSpace j a)).weq
      (boundedFlatAffineFullOpenRestriction j a) :=
  boundedFlatPerfectOpenRestriction_exact (inclusion j a)

end Quillen.PerfectComplexes
