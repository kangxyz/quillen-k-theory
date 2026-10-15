/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.GilletWaldhausen.SingleQuasiComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.VectorBundleInclusion

/-! # The existing strict-perfect single map is the actual coarse single map

On an arbitrary scheme the original bounded-termwise finite-locally-free
predicate is the existing strict-perfect predicate. The original degree-zero
single functors agree, and their canonical normalized KMaps agree. The
result is the actual fine/change-of-weak/coarse triangle for the previously
constructed vector-bundle S-comparison map; no equivalence is asserted.
-/
@[expose] public section

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

/-- The existing strict comparison uses exactly the actual coarse single KMap. -/
theorem vectorBundleSComparison_eq_coarseSingle (X : Scheme.{u}) (k : ℕ) :
    vectorBundleSComparison X k =
      KMap (boundedTermsSingle_coarseExact.{u,u+1}
        (AlgebraicGeometry.Scheme.Modules.finiteLocallyFree X) 0) k :=
  KMap_eq_of_iso (vectorBundleInclusion_waldhausenExact X)
    (boundedTermsSingle_coarseExact.{u,u+1} (AlgebraicGeometry.Scheme.Modules.finiteLocallyFree X)
      0)
    (eqToIso (vectorBundleInclusion_eq_boundedTermsSingle X)) k

/-- The exact public strict-perfect map is the actual change-of-weak KMap
composed with the original fine degree-zero single KMap. -/
theorem vectorBundleSComparison_eq_changeWeak_comp_fineSingle (X : Scheme.{u}) (k : ℕ) :
    vectorBundleSComparison X k =
      (KMap (Fibration.changeWeak_exact (boundedTermsNested
        (AlgebraicGeometry.Scheme.Modules.finiteLocallyFree X)))
        k).comp
        (KMap (boundedTermsSingleExactFunctor.{u,u+1}
          (AlgebraicGeometry.Scheme.Modules.finiteLocallyFree X)
          0).waldhausenExact k) :=
  (vectorBundleSComparison_eq_coarseSingle X k).trans
    (boundedTermsSingle_coarse_KMap.{u,u+1} (AlgebraicGeometry.Scheme.Modules.finiteLocallyFree X) 0
      k)

end Quillen.PerfectComplexes
