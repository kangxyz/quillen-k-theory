/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.KTheory
public import Quillen.AlgebraicGeometry.Scheme.Comparison.SmallVectorBundleK
public import Quillen.Waldhausen.QuillenComparison.Equivalence

/-!
# Canonical maps from public scheme K to perfect-complex K

The actual small-model Q-equivalence and proved Q/S comparison identify
public scheme K with the existing vector-bundle S-theory. Composing the
actual degree-zero maps gives comparison homomorphisms to strict and locally
perfect complexes. Their equivalence is the separate Gillet–Waldhausen and
strict/local comparison problem; it is not asserted here.
-/
@[expose] public section

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts
universe u

namespace Quillen.PerfectComplexes

/-- Public scheme K is canonically the exact vector-bundle S-theory. -/
def vectorBundleQSEquiv (X : Scheme.{u}) (n : ℕ) :
    Quillen.Scheme.K X n ≃*
      (Waldhausen.ofExactCategory (SchemeSheaf.vectorBundleExactStructure X)).K n :=
  (SchemeSheaf.smallVectorBundleKEquiv X n).trans
    (Waldhausen.QuillenComparison.comparisonKEquiv (SchemeSheaf.vectorBundleExactStructure X)
      n).symm

/-- The monoid-hom coercion is the canonical forward map. -/
@[simp] theorem vectorBundleQSEquiv_coe (X : Scheme.{u}) (n : ℕ) :
    ↑(vectorBundleQSEquiv X n) =
      (Waldhausen.QuillenComparison.comparisonKEquiv
        (SchemeSheaf.vectorBundleExactStructure X) n).symm.toMonoidHom.comp
          (SchemeSheaf.smallVectorBundleKMap X n) := rfl

/-- The canonical degree-zero comparison from public scheme K to strict-perfect K. -/
def vectorBundleToStrictKMap (X : Scheme.{u}) (n : ℕ) :
    Quillen.Scheme.K X n →* StrictK X n :=
  (vectorBundleSComparison X n).comp (vectorBundleQSEquiv X n).toMonoidHom

/-- The canonical degree-zero comparison from public scheme K to locally-perfect K. -/
def vectorBundleToPerfectKMap (X : Scheme.{u}) (n : ℕ) :
    Quillen.Scheme.K X n →* PerfectK X n :=
  (vectorBundleToPerfectSMap X n).comp (vectorBundleQSEquiv X n).toMonoidHom

/-- The two canonical degree-zero maps commute with the existing strict/local map. -/
@[simp] theorem strictToPerfect_comp_vectorBundleToStrictKMap
    (X : Scheme.{u}) (n : ℕ) :
    (strictToPerfectKMap X n).comp (vectorBundleToStrictKMap X n) =
      vectorBundleToPerfectKMap X n := rfl

end Quillen.PerfectComplexes
