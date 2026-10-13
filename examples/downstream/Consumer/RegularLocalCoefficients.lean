/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.LocalCoefficients.RegularGroupRing
public import Quillen.Topology.LocalCoefficients.RegularUniverseLift

/-!
# Independent regular-coefficient client

The actual regular monodromy detects commutation of loop classes. Its group-ring
formula retains the left-multiplication order, while lifted coefficients retain
inverse transport and allow unrelated spaces to share a sufficient universe.
-/

@[expose] public section

noncomputable section

open CategoryTheory Quillen.LocalCoefficients
open scoped Topology

universe u v w

namespace Consumer.RegularLocalCoefficients

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Commutativity is detected by the faithful action, rather than imposed on the group. -/
theorem monodromy_commutes_iff (b : X) (g h : π_ 1 X b) :
    regularPiOneMonodromy b g * regularPiOneMonodromy b h =
      regularPiOneMonodromy b h * regularPiOneMonodromy b g ↔ g * h = h * g := by
  constructor
  · intro e
    apply regularPiOneMonodromy_injective b
    simpa only [map_mul] using e
  · intro e
    simpa only [map_mul] using congrArg (regularPiOneMonodromy b) e

/-- Postcomposition acts on the left in the original fundamental-group convention. -/
theorem groupRing_action_order (b : X) (g h : π_ 1 X b) (n : ℤ) :
    regularFiberGroupRingEquiv b
        ((regularPiOneMonodromy b g).asHom
          (regularSingle b (HomotopyGroup.pi1MulEquivFundamentalGroup h) n)) =
      MonoidAlgebra.single (g * h) n :=
  regularFiberGroupRingEquiv_monodromy_single b g h n

/-- Inverse path transport survives coefficient lifting to the displayed larger universe. -/
theorem lifted_transport_inverse (b : X) {x y : X} (q : Path x y)
    (a : fiber (regularLift.{u, v} b) x) :
    transport (regularLift.{u, v} b) q.symm
      (transport (regularLift.{u, v} b) q a) = a := by
  apply (regularLiftFiberEquiv b x).injective
  simp only [regularLiftFiberEquiv_transport]
  exact regular_transport_symm_transport b q (regularLiftFiberEquiv b x a)

/-- Independent spatial universes admit a common sufficient coefficient universe. -/
def commonCoefficientSystems (b : X) (c : Y) :
    System.{u, max u v w} X × System.{v, max u v w} Y :=
  (regularLift.{u, max v w} b, regularLift.{v, max u w} c)

end Consumer.RegularLocalCoefficients
