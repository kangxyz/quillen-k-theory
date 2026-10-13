/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Covering.HomotopyGroups

/-! Degree, endpoint-cast, actual representative, and non-surjective-cover guards. -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open Convexity
universe u v

namespace QuillenTest.CoverHomotopyDescent

open Quillen
variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
variable {p : E → B} (hp : IsCoveringMap p)

/-- Degree two retains an arbitrary point-dependent equality of basepoints. -/
theorem degreeTwo (e : E) (b : B) (he : p e = b) :
    Function.Bijective (homotopyGroupMap (N := Fin 2) (Covering.projection hp) he) :=
  Covering.homotopyGroupMap_projection_bijective hp (by omega) e he

/-- Degree three retains the actual original group map without any total-space connectivity. -/
theorem degreeThree (e : E) :
    Function.Bijective (piMap 2 (Covering.projection hp) (x := e) rfl) :=
  Covering.homotopyGroupMap_projection_bijective hp (by omega) e rfl

/-- The lift is fixed at the supplied point on the entire geometric boundary. -/
theorem entireBoundary (n : ℕ) (hn : 2 ≤ n) (e : E) {b : B} (he : p e = b)
    (σ : SphericalSimplex B b n) (x : StdSimplex ℝ (Fin (n + 1)))
    (hx : x ∈ simplexBoundary n) : Covering.sphericalLift hp hn e he σ x = e :=
  (Covering.sphericalLift hp hn e he σ).boundary x hx

/-- Projection after lifting is literally the original chosen cube representative. -/
theorem originalCubeImage (n : ℕ) (hn : 2 ≤ n) (e : E) {b : B} (he : p e = b)
    (σ : SphericalSimplex B b n) :
    genLoopPostcomp (Covering.projection hp) he
      (Covering.sphericalLift hp hn e he σ).toGenLoop = σ.toGenLoop := by
  rw [← SphericalSimplex.toGenLoop_map, Covering.projection_sphericalLift]

/-- The index restriction specifically excludes a spurious Pi one isomorphism claim. -/
theorem degreeOneExcluded : ¬ (2 : ℕ) ≤ 1 := by omega

/-- Missing target components do not obstruct the based higher-degree projection result. -/
theorem nonSurjectivePointCover :
    ¬ Function.Surjective (fun _ : PUnit ↦ (false : Bool)) ∧
      Function.Bijective (homotopyGroupMap (N := Fin 2)
        (Covering.projection (IsCoveringMap.of_discreteTopology
          (fun _ : PUnit ↦ (false : Bool)))) (x := PUnit.unit) rfl) := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := h true
    exact Bool.false_ne_true hx
  · exact Covering.homotopyGroupMap_projection_bijective _ (by omega) PUnit.unit rfl

end QuillenTest.CoverHomotopyDescent
