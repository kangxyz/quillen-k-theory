/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.Topology.CWComplex.GlobalLifting

/-! # Independent original-map clients of global CW lifting -/
@[expose] public section

open Topology

open Quillen.ClassicalCW

noncomputable section
open Set
universe u v w
namespace Quillen.Consumer.CWGlobalLifting
open ClassicalCW
variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable (C : Set X) [CWComplex C]
variable {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]

/-- Genuine boundary lifting produces a continuous lift and its pointwise
original equation across independent source and target universes. -/
theorem actualContinuousLift (p : C(E, B)) (hp : CubicalSubdivision.BoundaryLifting p)
    (f : C(C, B)) : ∃ g : C(C, E), ∀ x, p (g x) = f x :=
  ⟨globalLift C p hp f, globalLiftFun_over C p hp f⟩

/-- The global lift retains the complete characteristic-coordinate evaluation,
not merely a homotopy class or a map from a replacement CW model. -/
theorem actualCharacteristicBaseEquation (p : C(E, B))
    (hp : CubicalSubdivision.BoundaryLifting p) (f : C(C, B)) :
    ∃ g : C(C, E), ∀ n (i : RelCWComplex.cell C n) (z : CharacteristicDisk n),
      p (g (characteristicQuotient C ⟨n, i, z⟩)) =
        f (characteristicQuotient C ⟨n, i, z⟩) :=
  ⟨globalLift C p hp f, fun _ _ _ ↦ globalLiftFun_over C p hp f _⟩

end Quillen.Consumer.CWGlobalLifting
