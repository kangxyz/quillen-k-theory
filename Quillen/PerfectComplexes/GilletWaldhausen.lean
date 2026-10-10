/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.GilletWaldhausen.GeneralComparison
import Quillen.PerfectComplexes.SingleComparison
import Quillen.PerfectComplexes.QuillenComparison
import Quillen.Scheme.VectorBundle.KernelClosure

/-!
# The original scheme K to strict-perfect K comparison in every degree

The general universe bridge supplies the actual bounded-complex fiber theorem;
no regularity, quasi-compactness or resolution-property hypothesis is needed.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.GilletWaldhausen
attribute [local instance] Abelian.hasFiniteBiproducts
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.PerfectComplexes

/-- The original single-complex S-map is bijective for every scheme and K-degree. -/
theorem vectorBundleSComparison_bijective (X : Scheme.{u}) (n : ℕ) :
    Function.Bijective (vectorBundleSComparison X n) := by
  rw [vectorBundleSComparison_eq_coarseSingle]
  exact boundedTermsSingle_coarse_KMap_bijective_general (SchemeSheaf.finiteLocallyFree X) n

/-- The exact public comparison from scheme Q-theory to strict-perfect K is bijective. -/
theorem vectorBundleToStrictKMap_bijective (X : Scheme.{u}) (n : ℕ) :
    Function.Bijective (vectorBundleToStrictKMap X n) :=
  (vectorBundleSComparison_bijective X n).comp (vectorBundleQSEquiv X n).bijective

/-- The equivalence retains the actual public comparison as its forward map. -/
def vectorBundleToStrictKEquiv (X : Scheme.{u}) (n : ℕ) :
    Quillen.Scheme.K X n ≃* StrictK X n :=
  MulEquiv.ofBijective (vectorBundleToStrictKMap X n) (vectorBundleToStrictKMap_bijective X n)

@[simp] theorem vectorBundleToStrictKEquiv_toMonoidHom (X : Scheme.{u}) (n : ℕ) :
    (vectorBundleToStrictKEquiv X n).toMonoidHom = vectorBundleToStrictKMap X n := rfl

end Quillen.PerfectComplexes
