/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

import Quillen.Topology.LocalCoefficients.RegularUniverseLift
import Quillen.Topology.LocalCoefficients.RegularGroupRing

/-! Independent consumers of regular monodromy, path transport, and universe lifting. -/

noncomputable section

open CategoryTheory Quillen.LocalCoefficients
open scoped Topology

universe u v w

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

example (b : X) (g : FundamentalGroup X b) (h : regularMonodromy b g = 1) : g = 1 := by
  exact regularMonodromy_injective b (h.trans (map_one (regularMonodromy b)).symm)

/-- Noncommuting loops stay noncommuting; no commutative fundamental group is inferred. -/
example (b : X) (g h : FundamentalGroup X b) (hne : g * h ≠ h * g) :
    regularMonodromy b g * regularMonodromy b h ≠
      regularMonodromy b h * regularMonodromy b g := by
  intro e
  apply hne
  apply regularMonodromy_injective b
  simpa only [map_mul] using e

example (b : X) {x y : X} (q : Path x y)
    (p : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk x) (n : ℤ) :
    transport (regular b) q.symm
        (transport (regular b) q (regularSingle b p n)) = regularSingle b p n := by
  exact regular_transport_symm_transport b q (regularSingle b p n)

/-- Source and target in unrelated universes admit one common coefficient universe. -/
example (b : X) (c : Y) : System.{u, max u v w} X × System.{v, max u v w} Y :=
  (regularLift.{u, max v w} b, regularLift.{v, max u w} c)

example (b : X) {x y : X} (q : Path x y)
    (a : fiber (regularLift.{u, max v w} b) x) :
    regularLiftFiberEquiv b y (transport (regularLift.{u, max v w} b) q a) =
      transport (regular b) q (regularLiftFiberEquiv b x a) := by
  simp

example (b : X) (g h : FundamentalGroup X b)
    (e : (regularLift.{u, max v w} b).map g =
      (regularLift.{u, max v w} b).map h) : g = h :=
  regularLift_monodromy_injective b e

example (b : X) (g h : π_ 1 X b) (n : ℤ) :
    regularFiberGroupRingEquiv b
        ((regularPiOneMonodromy b g).asHom
          (regularSingle b (HomotopyGroup.pi1MulEquivFundamentalGroup h) n)) =
      MonoidAlgebra.single (g * h) n :=
  regularFiberGroupRingEquiv_monodromy_single b g h n

example (b : X) (g h : π_ 1 X b) (hne : g * h ≠ h * g) :
    regularPiOneMonodromy b g * regularPiOneMonodromy b h ≠
      regularPiOneMonodromy b h * regularPiOneMonodromy b g := by
  intro e
  apply hne
  apply regularPiOneMonodromy_injective b
  simpa only [map_mul] using e
