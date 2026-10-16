/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.BoundedTerms
public import Quillen.Aglib.Algebra.Homology.CochainComplex.ExactSubcategory.SingleInsertion
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Strict

/-!
# Native bounded terms and strict-perfect singles

The original finite-locally-free bounded-term predicate is strict perfectness, and the existing
degree-zero inclusions agree.-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open Quillen.Waldhausen
open Quillen.Waldhausen.GilletWaldhausen


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Quillen.PerfectComplexes
attribute [local instance] Abelian.hasFiniteBiproducts
open Waldhausen Waldhausen.GilletWaldhausen

/-- The two actual strict boundedness predicates agree on the original sheaf complexes. -/
theorem boundedTerms_finiteLocallyFree_eq_strictPerfect (X : Scheme.{u}) :
    boundedTerms (AlgebraicGeometry.Scheme.Modules.finiteLocallyFree X) = strictPerfect X := rfl

/-- The already constructed vector-bundle inclusion is the same original single functor. -/
theorem vectorBundleInclusion_eq_boundedTermsSingle (X : Scheme.{u}) :
    vectorBundleInclusion X = boundedTermsSingleFunctor.{u,u+1}
      (AlgebraicGeometry.Scheme.Modules.finiteLocallyFree X) 0
      := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end Quillen.PerfectComplexes

end

end
