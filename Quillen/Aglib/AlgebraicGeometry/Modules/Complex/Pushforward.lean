/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.Additive

/-! # Termwise direct image of module-sheaf complexes

The original complex direct-image functor has no perfection or exactness hypothesis.
Its existing namespace and declaration name are preserved for its geometric clients.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes

/-- Actual termwise direct image, without asserting it is exact. -/
def pushforwardComplex {U X : Scheme.{u}} (j : U ⟶ X) :
    CochainComplex U.Modules ℤ ⥤ CochainComplex X.Modules ℤ :=
  (Scheme.Modules.pushforward j).mapHomologicalComplex (.up ℤ)

end Quillen.PerfectComplexes
