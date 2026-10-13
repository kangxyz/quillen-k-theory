/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Covering.SingularSimplices
public import Quillen.Topology.HomotopyGroups.SphericalSimplexMap
public import Quillen.Topology.HomotopyGroups.WeakEquivalence
public import Quillen.Topology.Realization.EdgePathPresentation.SimplexCharts

/-!
# Actual covering projections on higher homotopy groups

A spherical simplex lifts uniquely after choosing a point over its basepoint.
For dimension at least two, its boundary is connected, so the actual simplex
lift is constant on that entire boundary. Relative homotopy lifting detects
exactly equality of the original homotopy classes. The resulting bijection is
for the original projection map, with any specified equality at its basepoint.
Neither surjectivity of the covering nor simple connectedness of its total
space is assumed. A commuting square then descends higher-degree bijectivity.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open Convexity
open scoped Simplicial
universe u v u' v'

namespace Quillen.Covering
variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B} (hp : IsCoveringMap p)

/-- The chosen first vertex belongs to the boundary in the retained dimension range. -/
theorem firstVertex_mem_boundary {n : ℕ} (hn : 2 ≤ n) :
    (StdSimplex.single 0 : StdSimplex ℝ (Fin (n + 1))) ∈ simplexBoundary n :=
  (simplexBoundary_joinedIn_vertices hn 0 0).source_mem

/-- The actual based simplex lift remains constant on the whole connected boundary. -/
def sphericalLift {n : ℕ} (hn : 2 ≤ n) (e : E) {b : B} (he : p e = b)
    (σ : SphericalSimplex B b n) : SphericalSimplex E e n := by
  have hv := firstVertex_mem_boundary hn
  have h₀ : p e = σ (StdSimplex.single 0) := he.trans (σ.boundary _ hv).symm
  let τ := lift hp (n := ⦋n⦌) σ.val e h₀
  refine ⟨τ, fun x hx ↦ ?_⟩
  have hproj (t : StdSimplex ℝ (Fin (n + 1))) : p (τ t) = σ t :=
    ContinuousMap.congr_fun (projection_lift hp σ.val e h₀) t
  have hconst : τ x = τ (StdSimplex.single 0) :=
    hp.constOn_of_comp (isPathConnected_simplexBoundary hn).isConnected.isPreconnected
      τ.continuous.continuousOn
      (fun a ha a' ha' ↦ (hproj a).trans
        ((σ.boundary a ha).trans ((σ.boundary a' ha').symm.trans (hproj a').symm)))
      hx hv
  exact hconst.trans (lift_vertex hp σ.val e h₀)

/-- Projection of the lifted spherical representative is exactly the original map. -/
@[simp] theorem projection_sphericalLift {n : ℕ} (hn : 2 ≤ n) (e : E) {b : B}
    (he : p e = b) (σ : SphericalSimplex B b n) :
    SphericalSimplex.map (projection hp) he (sphericalLift hp hn e he σ) = σ := by
  apply SphericalSimplex.ext
  intro x
  exact ContinuousMap.congr_fun (projection_lift hp σ.val e
    (he.trans (σ.boundary _ (firstVertex_mem_boundary hn)).symm)) x

/-- Lifting the projection recovers the actual spherical representative, before quotienting. -/
@[simp] theorem sphericalLift_projection {n : ℕ} (hn : 2 ≤ n) (e : E) {b : B}
    (he : p e = b) (σ : SphericalSimplex E e n) :
    sphericalLift hp hn e he (SphericalSimplex.map (projection hp) he σ) = σ := by
  apply Subtype.ext
  symm
  apply eq_lift hp
  · exact he.trans ((SphericalSimplex.map (projection hp) he σ).boundary _
      (firstVertex_mem_boundary hn)).symm
  · rfl
  · exact σ.boundary _ (firstVertex_mem_boundary hn)

/-- The original higher homotopy map of the supplied covering projection is
bijective at each supplied lift of a basepoint. -/
theorem homotopyGroupMap_projection_bijective {n : ℕ} (hn : 2 ≤ n)
    (e : E) {b : B} (he : p e = b) :
    Function.Bijective (homotopyGroupMap (N := Fin n) (projection hp) he) := by
  constructor
  · intro a a' haa'
    obtain ⟨σ, rfl⟩ := SphericalSimplex.homotopyClass_surjective a
    obtain ⟨σ', rfl⟩ := SphericalSimplex.homotopyClass_surjective a'
    rw [← SphericalSimplex.homotopyClass_map, ← SphericalSimplex.homotopyClass_map] at haa'
    apply (SphericalSimplex.homotopyClass_eq_iff σ σ').mpr
    let := simplyConnectedSpace_stdSimplex (Fin (n + 1))
    apply (hp.homotopicRel_iff_comp (f₀ := σ.val) (f₁ := σ'.val)
      ⟨StdSimplex.single 0, firstVertex_mem_boundary hn,
        (σ.boundary _ (firstVertex_mem_boundary hn)).trans
          (σ'.boundary _ (firstVertex_mem_boundary hn)).symm⟩).mpr
    exact (SphericalSimplex.homotopyClass_eq_iff _ _).mp haa'
  · intro a
    obtain ⟨σ, rfl⟩ := SphericalSimplex.homotopyClass_surjective a
    refine ⟨(sphericalLift hp hn e he σ).homotopyClass, ?_⟩
    rw [← SphericalSimplex.homotopyClass_map, projection_sphericalLift]

/-- In the positive-index convention, every shifted degree n+2 is an actual
projection group isomorphism; degree one is deliberately not asserted. -/
def piProjectionEquiv (m : ℕ) (e : E) {b : B} (he : p e = b) :
    HomotopyGroup.Pi (m + 2) E e ≃* HomotopyGroup.Pi (m + 2) B b :=
  MulEquiv.ofBijective (piMap (m + 1) (projection hp) he)
    (homotopyGroupMap_projection_bijective hp (by omega) e he)

@[simp] theorem piProjectionEquiv_apply (m : ℕ) (e : E) {b : B} (he : p e = b)
    (a : HomotopyGroup.Pi (m + 2) E e) :
    piProjectionEquiv hp m e he a = piMap (m + 1) (projection hp) he a := rfl

variable {E' : Type u'} {B' : Type v'} [TopologicalSpace E'] [TopologicalSpace B']
variable {p' : E' → B'} (hp' : IsCoveringMap p')

include hp hp' in
/-- A genuine commuting covering square descends higher-degree bijectivity
from its actual upstairs map, keeping the square's endpoint equality. -/
theorem homotopyGroupMap_base_bijective (k : C(E, E')) (f : C(B, B'))
    (h : ∀ x, p' (k x) = f (p x)) (e : E) {n : ℕ} (hn : 2 ≤ n)
    (hk : Function.Bijective (homotopyGroupMap (N := Fin n) k (x := e) rfl)) :
    Function.Bijective (homotopyGroupMap (N := Fin n) f (x := p e) rfl) := by
  have hsq : f.comp (projection hp) = (projection hp').comp k := by
    ext x
    exact (h x).symm
  have hcomm :
      homotopyGroupMap (N := Fin n) f (x := p e) rfl ∘
        homotopyGroupMap (N := Fin n) (projection hp) (x := e) rfl =
      homotopyGroupMap (N := Fin n) (projection hp') (h e) ∘
        homotopyGroupMap (N := Fin n) k (x := e) rfl := by
    funext a
    calc
      _ = homotopyGroupMap (N := Fin n) (f.comp (projection hp)) rfl a :=
        (homotopyGroupMap_comp (projection hp) rfl f rfl a).symm
      _ = homotopyGroupMap (N := Fin n) ((projection hp').comp k) (h e) a :=
        congrFun (homotopyGroupMap_congr hsq rfl (h e)) a
      _ = _ := homotopyGroupMap_comp k rfl (projection hp') (h e) a
  have h := (homotopyGroupMap_projection_bijective hp' hn (k e) (h e)).comp hk
  rw [← hcomm] at h
  exact (Function.Bijective.of_comp_iff _
    (homotopyGroupMap_projection_bijective hp hn e rfl)).mp h

end Quillen.Covering
