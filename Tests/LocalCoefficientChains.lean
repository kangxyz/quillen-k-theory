/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.Chains

/-!
# Consumers of genuine local-coefficient singular chains

These tests use the regular path-class coefficient system, in which transport
acts on generators by concatenation. They also check the signed one-simplex
boundary and the comparison with mathlib's ordinary singular chains.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Opposite Convexity
open scoped Simplicial

universe u

namespace Quillen.Tests.LocalCoefficientChains

open LocalCoefficients

variable {X : Type u} [TopologicalSpace X]

/-- A genuine coefficient system on path classes out of a chosen base point. -/
def regularSystem (b : X) (V : ModuleCat.{u} ℤ) : System.{u, u} X :=
  coyoneda.obj (op (FundamentalGroupoid.mk b)) ⋙ sigmaConst.obj V

/-- Transport in the regular system permutes path-class generators by
concatenation. It has not been replaced by constant coefficients. -/
theorem regular_transport_generator (b : X) (V : ModuleCat.{u} ℤ) {x y : X}
    (q : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk x) (p : Path x y) :
    Sigma.ι (fun _ : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk x ↦ V) q ≫
        transport (regularSystem b V) p =
      Sigma.ι (fun _ : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk y ↦ V)
        (q ≫ Path.Homotopic.Quotient.mk p) := by
  simp [regularSystem, transport, sigmaConst, Sigma.map']

/-- A one-simplex boundary moves the coefficient to its terminal vertex
with a positive sign and retains its initial coefficient with a negative sign. -/
theorem one_simplex_boundary (A : System.{u, u} X) (σ : SingularSimplex X ⦋1⦌) :
    chainInclusion A σ ≫ (singularChainComplex A).d 1 0 =
      restrictionTransport A σ (SimplexCategory.δ 0) ≫
          chainInclusion A (restrictSimplex σ (SimplexCategory.δ 0)) -
        restrictionTransport A σ (SimplexCategory.δ 1) ≫
          chainInclusion A (restrictSimplex σ (SimplexCategory.δ 1)) := by
  rw [chainInclusion_d]
  simp [Fin.sum_univ_two, sub_eq_add_neg]

/-- The boundary of a local-coefficient triangle has zero boundary. -/
theorem triangle_boundary_boundary (A : System.{u, u} X) (σ : SingularSimplex X ⦋2⦌) :
    (chainInclusion A σ ≫ (singularChainComplex A).d 2 1) ≫
      (singularChainComplex A).d 1 0 = 0 := by
  rw [Category.assoc, singularChainComplex_d_squared]
  simp

/-- The constant comparison has the exact existing mathlib target, not a
separately defined proxy for ordinary singular homology. -/
def ordinary_comparison (V : ModuleCat.{u} ℤ) :
    singularChainComplex (constant X V) ≅
      ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{u} ℤ)).obj V).obj
        (TopCat.of X) :=
  constantChainComplexIso V

end Quillen.Tests.LocalCoefficientChains
