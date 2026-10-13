/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.Regular
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# The regular basepoint fiber and the fundamental-group ring

This identifies the regular fiber with the integral group ring on the existing
first homotopy group using `HomotopyGroup.pi1MulEquivFundamentalGroup`.
Mathlib's reverse-concatenation multiplication makes postcomposition act by
left multiplication on basis vectors, with no abelian-group hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped Topology

universe u

namespace Quillen.LocalCoefficients

variable {X : Type u} [TopologicalSpace X]

/-- The regular fiber is the integral group ring on the original first homotopy group. -/
def regularFiberGroupRingEquiv (b : X) :
    fiber (regular b) b ≃ₗ[ℤ] MonoidAlgebra ℤ (π_ 1 X b) :=
  (Finsupp.mapDomain.linearEquiv ℤ ℤ
    (HomotopyGroup.pi1MulEquivFundamentalGroup (X := X) (x := b)).symm.toEquiv).trans
      (MonoidAlgebra.coeffLinearEquiv ℤ).symm

/-- The fiber identification relabels precisely the original loop classes. -/
@[simp]
theorem regularFiberGroupRingEquiv_single (b : X) (g : π_ 1 X b) (n : ℤ) :
    regularFiberGroupRingEquiv b
        (regularSingle b (HomotopyGroup.pi1MulEquivFundamentalGroup g) n) =
      MonoidAlgebra.single g n := by
  change MonoidAlgebra.ofCoeff
      (Finsupp.mapDomain HomotopyGroup.pi1MulEquivFundamentalGroup.symm
        (Finsupp.single (HomotopyGroup.pi1MulEquivFundamentalGroup g) n)) = _
  rw [Finsupp.mapDomain_single, MulEquiv.symm_apply_apply]
  rfl

/-- The actual first homotopy group acts through its canonical loop-class equivalence. -/
def regularPiOneMonodromy (b : X) : π_ 1 X b →* End (fiber (regular b) b) :=
  (regularMonodromy b).comp HomotopyGroup.pi1MulEquivFundamentalGroup.toMonoidHom

/-- This is a faithful action of the possibly nonabelian first homotopy group. -/
theorem regularPiOneMonodromy_injective (b : X) :
    Function.Injective (regularPiOneMonodromy b) :=
  (regularMonodromy_injective b).comp HomotopyGroup.pi1MulEquivFundamentalGroup.injective

/-- Under the group-ring identification, transport is left multiplication on generators. -/
theorem regularFiberGroupRingEquiv_monodromy_single (b : X) (g h : π_ 1 X b) (n : ℤ) :
    regularFiberGroupRingEquiv b
        ((regularPiOneMonodromy b g).asHom
          (regularSingle b (HomotopyGroup.pi1MulEquivFundamentalGroup h) n)) =
      MonoidAlgebra.single (g * h) n := by
  change regularFiberGroupRingEquiv b
      ((regularMonodromy b (HomotopyGroup.pi1MulEquivFundamentalGroup g)).asHom
        (regularSingle b (HomotopyGroup.pi1MulEquivFundamentalGroup h) n)) = _
  rw [regularMonodromy_single, ← map_mul, regularFiberGroupRingEquiv_single]

end Quillen.LocalCoefficients
