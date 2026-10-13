/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.Regular
public import Quillen.Topology.LocalCoefficients.CoefficientLift

/-!
# Regular coefficients in a sufficient universe

The regular system of a space in `Type u` is placed in `ModuleCat.{max u v} ℤ`
by the existing fully faithful module lift. Its fiber equivalence is natural
for the original path classes and faithful monodromy survives the lift.
No claim that a small-universe certificate controls arbitrary larger systems
is made.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

universe u v

namespace Quillen.LocalCoefficients

variable {X : Type u} [TopologicalSpace X]

/-- The regular local system in any displayed sufficient coefficient universe. -/
def regularLift (b : X) : System.{u, max u v} X :=
  coefficientLift.{u, u, v} (regular b)

/-- Explicit comparison with the original path-class free module. -/
def regularLiftFiberEquiv (b x : X) :
    fiber (regularLift.{u, v} b) x ≃ₗ[ℤ] fiber (regular b) x :=
  coefficientLiftFiberEquiv (regular b) x

/-- The lift preserves the actual postcomposition formula on every basis vector. -/
@[simp]
theorem regularLift_map_single (b : X) {x y : FundamentalGroupoid X}
    (q : x ⟶ y) (p : FundamentalGroupoid.mk b ⟶ x) (n : ℤ) :
    (regularLift.{u, v} b).map q (ULift.up (regularSingle b p n)) =
      ULift.up (regularSingle b (p ≫ q) n) := by
  apply ULift.ext
  exact regular_map_single b q p n

/-- The explicit cross-universe fiber equivalence is natural for actual paths. -/
@[simp]
theorem regularLiftFiberEquiv_transport (b : X) {x y : X} (p : Path x y)
    (a : fiber (regularLift.{u, v} b) x) :
    regularLiftFiberEquiv b y (transport (regularLift.{u, v} b) p a) =
      transport (regular b) p (regularLiftFiberEquiv b x a) := rfl

/-- The original fundamental group acts faithfully after every sufficient lift. -/
theorem regularLift_monodromy_injective (b : X) :
    Function.Injective ((regularLift.{u, v} b).mapEnd (FundamentalGroupoid.mk b)) := by
  intro g h e
  apply regularMonodromy_injective b
  exact coefficientLift_map_injective (regular b) e

end Quillen.LocalCoefficients
