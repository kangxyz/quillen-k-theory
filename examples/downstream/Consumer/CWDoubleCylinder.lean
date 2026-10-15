/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.DoubleMappingCylinder.CWLifting

/-! # Independent clients of the actual double-cylinder lift -/
@[expose] public section

open Topology

open Quillen.DoubleCylinder

noncomputable section
open CategoryTheory Limits MonoidalCategory Set
open scoped unitInterval
universe u
namespace Quillen.Consumer.CWDoubleCylinder
open DoubleCylinder
variable {X₀ X₁ X₂ : Type u}
variable [TopologicalSpace X₀] [TopologicalSpace X₁] [TopologicalSpace X₂]
variable [T2Space X₀] [T2Space X₁] [T2Space X₂]
variable (A : Set X₀) (B : Set X₁) (C : Set X₂)
variable [CWComplex A] [CWComplex B] [CWComplex C]
variable {D : TopCat.{u}} (f : TopCat.of A ⟶ TopCat.of B) (g : TopCat.of A ⟶ TopCat.of C)
variable {l : TopCat.of A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
variable (sq : IsPushout (intervalEndpoints (TopCat.of A)) (endMap f g) l e)
variable {E T : Type u} [TopologicalSpace E] [TopologicalSpace T]
variable (p : C(E, T)) (hp : CubicalSubdivision.BoundaryLifting p) (d : C(D, T))

include A B C f g sq hp in
/-- Arbitrary actual finite boundary lifting supplies an actual global lift on D. -/
theorem originalMapLifts : ∃ q : C(D, E), p.comp q = d :=
  exists_cwLift A B C f g sq p hp d

include A B C f g sq hp in
/-- An independently imported client retains the whole original cylinder equation. -/
theorem originalCylinderLifts : ∃ q : C(D, E), p.comp q = d ∧
    ∀ (t : I) (a : A), q (l (a, ULift.up t)) =
      cwLiftCylinderHomotopy A B C f g sq p hp d (t, a) :=
  ⟨cwLift A B C f g sq p hp d, cwLift_comp A B C f g sq p hp d,
    cwLift_cylinder A B C f g sq p hp d⟩

end Quillen.Consumer.CWDoubleCylinder
