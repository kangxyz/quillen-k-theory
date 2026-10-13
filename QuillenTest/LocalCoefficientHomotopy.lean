/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.Homotopy
public import QuillenTest.LocalCoefficientChains

/-!
# Consumers of transported local-coefficient chain homotopies

The endpoint conversion is checked on actual simplex summands. The chain
homotopy is also instantiated with the regular path-class coefficient system,
so the construction does not require constant coefficients.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Convexity
open scoped Simplicial

universe u

namespace QuillenTest.LocalCoefficientHomotopy

open Quillen

open LocalCoefficients

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)}

/-- Endpoint conversion transports each coefficient along its homotopy track. -/
theorem endpoint_conversion_on_simplex (H : f.Homotopy g) (A : System.{u, u} Y)
    (n : ℕ) (σ : SingularSimplex X ⦋n⦌) :
    chainInclusion (pullback f A) σ ≫ (homotopyPullbackChainIso H A).hom.f n =
      transport A (H.evalAt (σ (StdSimplex.single 0))) ≫
        chainInclusion (pullback g A) σ := by
  change chainInclusion (pullback f A) σ ≫
      coefficientModuleMap (homotopyPullbackIso H A).hom ⦋n⦌ = _
  rw [chainInclusion_coefficientModuleMap]
  rfl

/-- The actual endpoint chain homotopy applies to the path-class regular system. -/
def regular_chain_homotopy (H : f.Homotopy g) (b : Y) (V : ModuleCat.{u} ℤ) :
    _root_.Homotopy
      (pushforwardChainMap f (LocalCoefficientChains.regularSystem b V))
      ((homotopyPullbackChainIso H (LocalCoefficientChains.regularSystem b V)).hom ≫
        pushforwardChainMap g (LocalCoefficientChains.regularSystem b V)) :=
  pushforwardChainHomotopy H (LocalCoefficientChains.regularSystem b V)

end QuillenTest.LocalCoefficientHomotopy
