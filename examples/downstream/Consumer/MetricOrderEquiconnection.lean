/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.MetricOrderComplex.Equiconnection
public import Mathlib.Topology.Homotopy.Basic

/-!
# Actual homotopies between overlapping families

The independent client constructs a displayed homotopy between any two
continuous families which have positive common mass pointwise. Its topology
is the original one, its endpoints are the two specified maps, and every point
where they agree remains fixed. The connector also gives a continuous family
in the actual compact-open mapping space C(I,M).
-/

@[expose] public section
noncomputable section

open Quillen Quillen.MetricOrderComplex
open scoped Topology unitInterval

universe u v
namespace Consumer.MetricOrderEquiconnection

variable {P : Type u} [PartialOrder P] {A : Type v} [TopologicalSpace A]

/-- The genuine compact-open family of connector paths. -/
def connectorFamily : C(OverlappingPairs P, C(I, MetricOrderComplex P)) := connector.curry

/-- Currying changes neither the chosen points nor the connector time. -/
theorem connectorFamily_apply (z : OverlappingPairs P) (t : I) :
    connectorFamily z t = connectorPath z.1.1 z.1.2 z.2 t := rfl

/-- The whole diagonal becomes the constant family in the actual compact-open topology. -/
theorem connectorFamily_diagonal (x : MetricOrderComplex P) :
    connectorFamily ⟨(x, x), by simp⟩ = ContinuousMap.const I x := by
  apply ContinuousMap.ext
  intro t
  exact connector_diagonal x t

/-- A displayed homotopy between the original overlapping continuous maps. -/
def overlapHomotopy (f g : C(A, MetricOrderComplex P))
    (h : ∀ a, 0 < commonMass (f a) (g a)) : f.Homotopy g where
  toFun z := connector (⟨(f z.2, g z.2), h z.2⟩, z.1)
  continuous_toFun := by
    have hc : Continuous (fun z : I × A ↦
        ((⟨(f z.2, g z.2), h z.2⟩ : OverlappingPairs P), z.1)) := by fun_prop
    exact connector.continuous.comp hc
  map_zero_left a := connector_zero ⟨(f a, g a), h a⟩
  map_one_left a := connector_one ⟨(f a, g a), h a⟩

/-- Every point where the original maps agree is fixed for all homotopy times. -/
theorem overlapHomotopy_fixed (f g : C(A, MetricOrderComplex P))
    (h : ∀ a, 0 < commonMass (f a) (g a)) (a : A) (ha : f a = g a) (t : I) :
    overlapHomotopy f g h (t, a) = f a := by
  have hh (x y : MetricOrderComplex P) (hp : 0 < commonMass x y) (he : x = y) :
      connectorPath x y hp t = x := by
    subst y
    rw [connectorPath_self]
    rfl
  exact hh (f a) (g a) (h a) ha

/-- Pointwise distance less than two suffices; no chain union is required. -/
theorem homotopic_of_dist_lt_two (f g : C(A, MetricOrderComplex P))
    (h : ∀ a, dist (f a) (g a) < 2) : f.Homotopic g :=
  ⟨overlapHomotopy f g (fun a ↦ (commonMass_pos_iff_dist_lt_two _ _).mpr (h a))⟩

/-- The construction also applies to uncountable posets without local finiteness. -/
theorem uncountable_poset_homotopic (f g : C(A, MetricOrderComplex (Set ℝ)))
    (h : ∀ a, dist (f a) (g a) < 2) : f.Homotopic g := homotopic_of_dist_lt_two f g h

end Consumer.MetricOrderEquiconnection
