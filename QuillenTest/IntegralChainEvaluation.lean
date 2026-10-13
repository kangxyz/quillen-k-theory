/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.SphericalRelativeCycle
public import Quillen.Topology.LocalCoefficients.StraightenedIntegralEvaluation

/-! # Integral signs, original relative cycles, and exact spherical faces -/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Quillen Quillen.LocalCoefficients Convexity
open scoped Simplicial

variable {X : Type} [TopologicalSpace X]

/-- Negative coefficients remain the original integer multiples. -/
theorem regression_negative_coefficient (τ : SingularSimplex X ⦋2⦌) :
    integralChainEvaluation 2 (fun _ ↦ (1 : ℤ))
      (chainInclusion (constant X integralCoefficientModule.{0}) τ (ULift.up (-3))) = -3 := by
  rw [integralChainEvaluation_inclusion]
  norm_num

/-- A spherical 2-simplex is a genuine point-relative cycle, with the same generator. -/
theorem regression_spherical_relative_generator (z : X) (f₀ : SphericalSimplex X z 2) :
    (relativeSingularChainComplex {z} (constant X integralCoefficientModule.{0})).iCycles 2
      (sphericalRelativeCycle f₀) =
        (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
          (constant X integralCoefficientModule.{0}))).f 2
          (chainInclusion (constant X integralCoefficientModule.{0}) f₀.val (ULift.up 1)) :=
  iCycles_sphericalRelativeCycle f₀

/-- Four tetrahedral faces retain the literal increasing vertex parametrizations. -/
theorem regression_four_actual_faces (z : X) (τ : C(StdSimplex ℝ (Fin 4), X))
    (hτ : ∀ x ∈ simplexSkeleton 2 3, τ x = z) (i : Fin 4)
    (x : StdSimplex ℝ (Fin 3)) : sphericalFace τ hτ i x = τ (x.map i.succAbove) := rfl

/-- Equal original point-relative chains have equal evaluation without any
straightening chain map or coefficient homotopy. -/
theorem regression_original_relative_equality (z : X) (v : SingularSimplex X ⦋2⦌ → ℤ)
    (hv : v (ContinuousMap.const _ z) = 0)
    (a b : chainModule (constant X integralCoefficientModule.{0}) ⦋2⦌)
    (hab : (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
      (constant X integralCoefficientModule.{0}))).f 2 a =
      (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
        (constant X integralCoefficientModule.{0}))).f 2 b) :
    integralChainEvaluation 2 v a = integralChainEvaluation 2 v b :=
  integralChainEvaluation_eq_of_pointRelative_eq z 2 v hv a b hab

/-- The unnormalized absolute boundary of a constant 2-simplex is not dropped:
its signed evaluation is +1-1+1 = 1 before passing to the relative quotient. -/
theorem regression_constant_two_absolute_boundary (z : X) :
    integralChainEvaluation 1 (fun _ ↦ (1 : ℤ))
      ((singularChainComplex (constant X integralCoefficientModule.{0})).d 2 1
        (chainInclusion (constant X integralCoefficientModule.{0})
          (ContinuousMap.const _ z) (ULift.up 1))) = 1 := by
  rw [integralChainEvaluation_boundary]
  norm_num [Fin.sum_univ_succ]
