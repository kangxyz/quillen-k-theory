/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.LocalCoefficients.CoveringNaturality

/-!
# Independent client of regular covering chains

Different raw carrier universes are explicitly brought into the common
model universe. The supplied covering is on those stated models; this
client does not silently assert a universal-cover existence theorem.
-/

open CategoryTheory Convexity Quillen.LocalCoefficients
open scoped Simplicial

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {p : ULift.{v} E → ULift.{u} B} (hp : IsCoveringMap p)
variable [SimplyConnectedSpace (ULift.{v} E)] (e₀ : ULift.{v} E)

-- Integral coefficients and both chain models live in max u v, without shrinking carriers.
example :
    singularChainComplex (regular (p e₀)) ≅
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{max u v} ℤ)).obj
        (ModuleCat.of ℤ (ULift.{max u v} ℤ))).obj (TopCat.of (ULift.{v} E)) :=
  coveringChainIso hp e₀

-- The actual inverse recovers every original chain, not merely its homology class.
example (n : SimplexCategory) (c : chainModule (regular (p e₀)) n) :
    (coveringModuleIso hp e₀ n).inv ((coveringModuleIso hp e₀ n).hom c) = c :=
  ModuleCat.inv_hom_apply _ _

-- Iterated restrictions agree with one restriction by the actual composite operator.
example {l m n : SimplexCategory} (s : RegularSimplex (p e₀) n)
    (α : l ⟶ m) (β : m ⟶ n) :
    coveringRegularSimplexEquiv hp e₀ l
        (restrictRegularSimplex (p e₀) (restrictRegularSimplex (p e₀) s β) α) =
      restrictSimplex (coveringRegularSimplexEquiv hp e₀ n s) (α ≫ β) := by
  simp only [coveringRegularSimplexEquiv_restrict, restrictSimplex_comp]
