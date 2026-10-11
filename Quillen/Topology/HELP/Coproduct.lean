/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Mathlib.Topology.Homotopy.TopCat.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Explicit homotopy extension on topological subfamilies
-/
@[expose] public section


noncomputable section

open CategoryTheory Limits Opposite
open scoped Topology unitInterval

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Quillen

variable {ι : Type u} {X : ι → Type u} [∀ i, TopologicalSpace (X i)]

/-- The inclusion of an arbitrary subfamily of a topological disjoint union. -/
def sigmaSubfamilyInclusion (S : Set ι) : C((Σ i : S, X i.1), Σ i, X i) :=
  ContinuousMap.sigma fun i ↦ ContinuousMap.sigmaMk i.1

/-- Extend a prescribed homotopy on the selected components, keeping every
other component constant in time. -/
def sigmaSubfamilyHomotopyExtension {Y : Type v} [TopologicalSpace Y]
    (S : Set ι) (f : C((Σ i, X i), Y))
    (h : C(unitInterval × (Σ i : S, X i.1), Y)) :
    C(unitInterval × (Σ i, X i), Y) := by
  classical
  let component : ∀ i, C(X i × unitInterval, Y) := fun i ↦
    if hi : i ∈ S then
      h.comp (ContinuousMap.prodMk ContinuousMap.snd
        ((ContinuousMap.sigmaMk (⟨i, hi⟩ : S)).comp ContinuousMap.fst))
    else
      f.comp ((ContinuousMap.sigmaMk i).comp ContinuousMap.fst)
  let e : (unitInterval × Σ i, X i) ≃ₜ Σ i, X i × unitInterval :=
    (Homeomorph.prodComm _ _).trans Homeomorph.sigmaProdDistrib
  exact (ContinuousMap.sigma component).comp e

/-- The extension agrees with the supplied homotopy on its whole prescribed domain. -/
theorem sigmaSubfamilyHomotopyExtension_restrict {Y : Type v} [TopologicalSpace Y]
    (S : Set ι) (f : C((Σ i, X i), Y))
    (h : C(unitInterval × (Σ i : S, X i.1), Y))
    (t : unitInterval) (x : Σ i : S, X i.1) :
    Quillen.sigmaSubfamilyHomotopyExtension S f h (t, Quillen.sigmaSubfamilyInclusion S x) = h (t,
      x) := by
  rcases x with ⟨⟨i, hi⟩, x⟩
  simp [Quillen.sigmaSubfamilyHomotopyExtension, Quillen.sigmaSubfamilyInclusion, hi]

/-- Compatibility at time zero suffices for the explicit extension to start
at the original map everywhere. -/
theorem sigmaSubfamilyHomotopyExtension_zero {Y : Type v} [TopologicalSpace Y]
    (S : Set ι) (f : C((Σ i, X i), Y))
    (h : C(unitInterval × (Σ i : S, X i.1), Y))
    (hzero : ∀ x, h (0, x) = f (Quillen.sigmaSubfamilyInclusion S x))
    (x : Σ i, X i) :
    Quillen.sigmaSubfamilyHomotopyExtension S f h (0, x) = f x := by
  classical
  rcases x with ⟨i, x⟩
  by_cases hi : i ∈ S
  · simpa [Quillen.sigmaSubfamilyHomotopyExtension, Quillen.sigmaSubfamilyInclusion, hi] using
      hzero ⟨⟨i, hi⟩, x⟩
  · simp [Quillen.sigmaSubfamilyHomotopyExtension, hi]

/-- The subfamily inclusion has the genuine homotopy extension property
against every target space; no extension is assumed as input. -/
theorem sigmaSubfamily_homotopyExtension {Y : Type v} [TopologicalSpace Y]
    (S : Set ι) (f : C((Σ i, X i), Y))
    (h : C(unitInterval × (Σ i : S, X i.1), Y))
    (hzero : ∀ x, h (0, x) = f (Quillen.sigmaSubfamilyInclusion S x)) :
    ∃ k : C(unitInterval × (Σ i, X i), Y),
      (∀ x, k (0, x) = f x) ∧
      ∀ t x, k (t, Quillen.sigmaSubfamilyInclusion S x) = h (t, x) :=
  ⟨Quillen.sigmaSubfamilyHomotopyExtension S f h,
    Quillen.sigmaSubfamilyHomotopyExtension_zero S f h hzero,
    Quillen.sigmaSubfamilyHomotopyExtension_restrict S f h⟩


end Quillen
