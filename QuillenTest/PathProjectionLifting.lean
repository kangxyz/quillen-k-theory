/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyPullback.PathProjectionLifting

/-! # Prescribed endpoint, whole-path and lateral-boundary regressions -/
@[expose] public section
noncomputable section
open Quillen Quillen.HomotopyPullback
open scoped Topology unitInterval
universe u
namespace QuillenTest.PathProjectionLifting
variable {E B : Type u} [TopologicalSpace E] [TopologicalSpace B] {p : C(E, B)}

/-- Dimension zero gives a lift of an actual base path with both prescribed endpoints. -/
theorem prescribed_path_lift (hp : CubicalSubdivision.BoundaryLifting p)
    (x₀ x₁ : E) (γ : Path (p x₀) (p x₁)) :
    ∃ δ : Path x₀ x₁, p.comp δ.toContinuousMap = γ.toContinuousMap := by
  let z : HomotopyPullback p p := ⟨(x₁, x₀, γ.toContinuousMap), γ.source, γ.target⟩
  obtain ⟨l, hl⟩ := hp.pathProjection.surjective z
  refine ⟨⟨l, ?_, ?_⟩, ?_⟩
  · exact congrArg (fun z : HomotopyPullback p p ↦ z.val.2.1) hl
  · exact congrArg (fun z : HomotopyPullback p p ↦ z.val.1) hl
  · exact congrArg (fun z : HomotopyPullback p p ↦ z.val.2.2) hl

/-- The whole lateral family and both caps survive the higher-dimensional fill literally. -/
theorem full_boundary_data (hp : CubicalSubdivision.BoundaryLifting p) (n : ℕ)
    (a : C(CubicalSubdivision.Boundary n, C(I, E)))
    (b : C(CubicalSubdivision.Cube n, HomotopyPullback p p))
    (hab : ∀ z, pathProjection p (a z) = b z.val) :
    ∃ l : C(CubicalSubdivision.Cube n, C(I, E)),
      (∀ (z : CubicalSubdivision.Boundary n) (t : I), l z.val t = a z t) ∧
      (∀ x, l x 0 = (b x).val.2.1) ∧ (∀ x, l x 1 = (b x).val.1) ∧
      ∀ x t, p (l x t) = (b x).val.2.2 t := by
  obtain ⟨l, ha, hb⟩ := hp.pathProjection n a b hab
  refine ⟨l, fun z t ↦ ContinuousMap.congr_fun (ha z) t, ?_, ?_, ?_⟩
  · intro x
    exact congrArg (fun z : HomotopyPullback p p ↦ z.val.2.1)
      (ContinuousMap.congr_fun hb x)
  · intro x
    exact congrArg (fun z : HomotopyPullback p p ↦ z.val.1)
      (ContinuousMap.congr_fun hb x)
  · intro x t
    exact congrArg (fun z : HomotopyPullback p p ↦ z.val.2.2 t)
      (ContinuousMap.congr_fun hb x)

end QuillenTest.PathProjectionLifting
