/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.IntegralChainEvaluation
public import Quillen.Topology.Realization.RelativeSphericalStraightening

/-!
# Finite straightening gives a degreewise integral homotopy-class evaluation

In degree m+2 the target is the additive form of the original abelian homotopy
group. Selected actual simplices are evaluated by their constructed spherical
endpoints; unselected simplices are assigned zero. This function extends to all
original chains by the coproduct universal property. No chain map, global
straightening, or degree-one nonabelian linearization is claimed.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Convexity
open scoped Simplicial

universe u

namespace Quillen.LocalCoefficients

variable {X : Type u} [TopologicalSpace X]
variable {m N : ℕ} {z : X} {S F : FiniteSimplexFamily X} {hS : S.FaceClosed}

/-- Degreewise values on actual simplices, using the finite selected family.
The target is the existing Pi(m+2), with its abelian additive wrapper. -/
def straightenedSimplexValue
    (P : PartialSimplexStraightening (m + 2) z S F hS N) (hn : m + 2 < N)
    (τ : SingularSimplex X ⦋m + 2⦌) : Additive (HomotopyGroup.Pi (m + 2) X z) := by
  classical
  exact if hτ : τ ∈ S (m + 2) then
    (P.sphericalEndpoint hn ⟨τ, hτ⟩).additiveClass else 0

/-- Membership proofs do not split the value of an actual selected simplex. -/
theorem straightenedSimplexValue_selected
    (P : PartialSimplexStraightening (m + 2) z S F hS N) (hn : m + 2 < N)
    (τ : SingularSimplex X ⦋m + 2⦌) (hτ : τ ∈ S (m + 2)) :
    straightenedSimplexValue P hn τ = (P.sphericalEndpoint hn ⟨τ, hτ⟩).additiveClass := by
  classical
  simp [straightenedSimplexValue, hτ]

/-- Every selected fixed spherical input retains its actual original homotopy class. -/
theorem straightenedSimplexValue_fixed
    (P : PartialSimplexStraightening (m + 2) z S F hS N) (hn : m + 2 < N)
    (f₀ : SphericalSimplex X z (m + 2)) (h₀ : f₀.val ∈ S (m + 2))
    (hF : f₀.val ∈ F (m + 2)) : straightenedSimplexValue P hn f₀.val = f₀.additiveClass := by
  rw [straightenedSimplexValue_selected P hn f₀.val h₀]
  have h : P.sphericalEndpoint hn ⟨f₀.val, h₀⟩ = f₀ := by
    apply SphericalSimplex.ext
    intro x
    exact P.stationary (m + 2) _ hF x 1
  rw [h]

/-- A selected basepoint-constant simplex has zero evaluation. -/
theorem straightenedSimplexValue_const
    (P : PartialSimplexStraightening (m + 2) z S F hS N) (hn : m + 2 < N)
    (h₀ : ContinuousMap.const _ z ∈ S (m + 2))
    (hF : ContinuousMap.const _ z ∈ F (m + 2)) :
    straightenedSimplexValue P hn (ContinuousMap.const _ z) = 0 := by
  exact (straightenedSimplexValue_fixed P hn SphericalSimplex.const h₀ hF).trans
    (SphericalSimplex.additiveClass_const m)

/-- The degree-m+2 evaluation on the actual original constant-integral chain module. -/
def straightenedIntegralEvaluation
    (P : PartialSimplexStraightening (m + 2) z S F hS N) (hn : m + 2 < N) :
    chainModule (constant X integralCoefficientModule.{u}) ⦋m + 2⦌ ⟶
      ModuleCat.of ℤ (Additive (HomotopyGroup.Pi (m + 2) X z)) :=
  integralChainEvaluation (m + 2) (straightenedSimplexValue P hn)

/-- This evaluation kills the original point-subspace chain inclusion.
It is not a homotopy transporting coefficients between different simplices. -/
theorem pointPushforward_straightenedIntegralEvaluation
    (P : PartialSimplexStraightening (m + 2) z S F hS N) (hn : m + 2 < N)
    (h₀ : ContinuousMap.const _ z ∈ S (m + 2))
    (hF : ContinuousMap.const _ z ∈ F (m + 2)) :
    pushforwardModuleMap (subspaceInclusion {z}) (constant X integralCoefficientModule.{u})
      ⦋m + 2⦌ ≫ straightenedIntegralEvaluation P hn = 0 :=
  pointPushforward_integralChainEvaluation z (m + 2) (straightenedSimplexValue P hn)
    (straightenedSimplexValue_const P hn h₀ hF)

end Quillen.LocalCoefficients
