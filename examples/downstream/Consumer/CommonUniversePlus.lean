/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.PlusConstruction.CommonUniverse

/-! # Independent mixed-universe consumers of the original plus certificate

These transport the actual certificate and its actual maps. They do not
assert a new comparison equivalence or arbitrary coefficient enlargement.
-/
@[expose] public section
noncomputable section
universe u v w
namespace Consumer.CommonUniversePlus
open Quillen Quillen.LocalCoefficients
open Quillen.PlusConstruction.CommonUniverse

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- All original certificate fields are transported to the stated common universe. -/
theorem original_mixed_certificate (f : C(X, Y)) {x : X} {y : Y}
    (γ : Path (f x) y) (N : Subgroup (HomotopyGroup.Pi 1 X x))
    (h : IsPlusConstruction.{u, v, max u v w} f γ N) :
    IsPlusConstruction.{max u v w, max u v w, max u v w}
      (CommonUniverseChains.liftMap.{u, v, w} f) (liftPath f γ)
      (liftSubgroup.{u, max u v w} N) := isPlusConstruction f γ N h

/-- The concrete successor universe pattern needs no coefficient-only restriction. -/
theorem original_successor_certificate {Z : Type (u + 1)} [TopologicalSpace Z]
    (f : C(X, Z)) {x : X} {z : Z} (γ : Path (f x) z)
    (N : Subgroup (HomotopyGroup.Pi 1 X x))
    (h : IsPlusConstruction.{u, u + 1, u + 1} f γ N) :
    IsPlusConstruction.{u + 1, u + 1, u + 1}
      (CommonUniverseChains.liftMap.{u, u + 1, 0} f) (liftPath f γ)
      (liftSubgroup.{u, u + 1} N) := isPlusConstruction.{u, u + 1, 0} f γ N h

end Consumer.CommonUniversePlus
