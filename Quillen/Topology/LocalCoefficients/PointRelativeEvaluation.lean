/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.IntegralChainEvaluation
public import Quillen.Topology.LocalCoefficients.PointRelativeHomology
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Evaluating the original point-relative chain equation

An integral chain evaluation that kills the basepoint generator takes equal
values on chains with equal images in the original point-relative quotient.
The proof uses the genuine degreewise short exact sequence and does not
construct or assume a straightening chain homotopy.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits
open scoped Simplicial

universe u

namespace Quillen.LocalCoefficients

variable {X : Type u} [TopologicalSpace X]
variable {G : Type u} [AddCommGroup G]

/-- Equality in the original point-relative quotient can be evaluated by any
integral simplex value function which vanishes on the basepoint constant. -/
theorem integralChainEvaluation_eq_of_pointRelative_eq (z : X) (n : ℕ)
    (v : SingularSimplex X ⦋n⦌ → G) (hv : v (ContinuousMap.const _ z) = 0)
    (a b : chainModule (constant X integralCoefficientModule.{u}) ⦋n⦌)
    (hab : (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
      (constant X integralCoefficientModule.{u}))).f n a =
      (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
        (constant X integralCoefficientModule.{u}))).f n b) :
    integralChainEvaluation n v a = integralChainEvaluation n v b := by
  let E := HomologicalComplex.eval (ModuleCat.{u} ℤ) (ComplexShape.down ℕ) n
  have hS := (pointRelativeSequence_shortExact z integralCoefficientModule.{u}).map_of_exact E
  have hz : ((pointRelativeSequence z integralCoefficientModule.{u}).map E).g (a - b) = 0 := by
    change (cokernel.π (pushforwardChainMap (subspaceInclusion {z})
      (constant X integralCoefficientModule.{u}))).f n (a - b) = 0
    rw [map_sub, hab, sub_self]
  obtain ⟨c, hc⟩ := (ShortComplex.moduleCat_exact_iff _).mp hS.exact (a - b) hz
  apply sub_eq_zero.mp
  rw [← map_sub, ← hc]
  exact ConcreteCategory.congr_hom (pointPushforward_integralChainEvaluation z n v hv) c

end Quillen.LocalCoefficients
