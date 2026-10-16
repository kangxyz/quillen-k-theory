/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Basic


public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.Aglib.AlgebraicGeometry.Modules.Flat.Extensions
public import Aglib.AlgebraicGeometry.Modules.Flat.Closure
public import Aglib.AlgebraicGeometry.Modules.Complex.Flat.Resolution
public import Quillen.AlgebraicGeometry.PerfectComplexes.KTheory
public import Aglib.Algebra.Homology.CochainComplex.BoundedAbove.Basic

/-!
# The actual bounded-flat locally-perfect Waldhausen model

Objects retain their original sheaf complexes and chain maps, with explicit
termwise upper bound, stalkwise-flat terms and the original local-perfect
predicate. Actual extension closure gives ambient quotient cofibrations and
original quasi-isomorphisms. The honest inclusion into Perfect is exact;
no equivalence with that larger category is assumed here.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex



open CategoryTheory.ExactCategory



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes

variable {X : Scheme.{u}}

/-- Actual Waldhausen structure, with ambient admissible monomorphisms and original
  quasi-isomorphisms. -/
def boundedFlatPerfectWaldhausen (X : Scheme.{u}) : Waldhausen.Structure (BoundedFlatPerfect X) :=
  Waldhausen.complexSubcategory (boundedFlatPerfect X)

theorem boundedFlatPerfectInclusion_exact (X : Scheme.{u}) :
    Waldhausen.IsExact (boundedFlatPerfectWaldhausen X).cof (boundedFlatPerfectWaldhausen X).weq
      (perfectWaldhausen X).cof (perfectWaldhausen X).weq (boundedFlatPerfectInclusion X) :=
  Waldhausen.subcategoryInclusion_exact _ _ (fun _ h => h.1)

end Quillen.PerfectComplexes
