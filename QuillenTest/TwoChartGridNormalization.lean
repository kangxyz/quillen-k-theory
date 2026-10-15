/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.DoubleMappingCylinder.ColumnNormalization

/-!
# Original-map consumers of the full two-chart grid induction

The preceding-skeleton track is compared as an actual continuous path. Original overlap data
stay fixed, including the whole path at boundary parameters. The original double-cylinder
consumer retains its cylinder map and source point, and tests the asymmetric zero bound.
-/

@[expose] public section

open Quillen.CubicalSubdivision


noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u

namespace QuillenTest.TwoChartGridNormalization

open Quillen

open CubicalSubdivision

/-- The new stage keeps each whole old path as the identical continuous map. -/
theorem original_skeleton_path_unchanged {Y : Type u} [TopologicalSpace Y]
    {n mesh r : ℕ} {b : C(Cube n, Y)} {U V : Set Y} {a₁ b₁ a₂ b₂ : unitInterval} {p q : ℕ}
    (D : TwoChartStageHomotopy n mesh r b U V a₁ b₁ a₂ b₂ p q)
    (hab : a₁ < b₁) (hce : a₂ < b₂)
    (hUV : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : U // y.val ∈ V}, U)) p)
    (hVU : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : V // y.val ∈ U}, V)) q)
    (hcover : ∀ G : FaceIndex n mesh,
      (∀ s, b (face G s) ∈ U) ∨ ∀ s, b (face G s) ∈ V) :
    ∃ D' : TwoChartStageHomotopy n mesh (r + 1) b U V a₁ b₁ a₂ b₂ p q,
      ∀ (x : skeletonBelow n mesh r) (y : skeletonBelow n mesh (r + 1)), x.val = y.val →
        (⟨fun t ↦ D'.homotopy (t, y), by fun_prop⟩ : C(unitInterval, Y)) =
          ⟨fun t ↦ D.homotopy (t, x), by fun_prop⟩ := by
  obtain ⟨D', hD⟩ := D.exists_succ hab hce hUV hVU hcover
  exact ⟨D', fun x y hxy ↦ ContinuousMap.ext (fun t ↦ hD t x y hxy)⟩

/-- Original maps already in the overlap remain literally fixed on the whole cube. -/
theorem original_overlap_map_fixed (n mesh : ℕ) {Y : Type u} [TopologicalSpace Y]
    (b : C(Cube n, Y)) (U V : Set Y) (hb : ∀ x, b x ∈ U ∩ V)
    (a₁ b₁ a₂ b₂ : unitInterval) (hab : a₁ < b₁) (hce : a₂ < b₂) (p q : ℕ)
    (hUV : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : U // y.val ∈ V}, U)) p)
    (hVU : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : V // y.val ∈ U}, V)) q) :
    ∃ v : C(Cube n, Y), ∃ H : b.Homotopy v, ∀ t x, H (t, x) = b x := by
  obtain ⟨v, H, _, _, hfix, _, _⟩ := exists_two_chart_grid_normalization n mesh b U V
    a₁ b₁ a₂ b₂ hab hce p q hUV hVU (fun G ↦ Or.inl (fun s ↦ (hb (face G s)).1))
  refine ⟨v, H, ?_⟩
  intro t x
  obtain ⟨k, s, rfl⟩ := cell_covers n mesh x
  have h := hfix (maximalFace k) (fun v ↦ hb (face (maximalFace k) v)) t
    (fun i ↦ s i.val)
  simpa only [maximalFace_apply] using h

/-- The relative normalization keeps every original boundary path as an identical continuous
map for every deformation time, rather than preserving just its two endpoints. -/
theorem original_boundary_path_fixed (d : ℕ) {Y : Type u} [TopologicalSpace Y]
    (b : C(Cube (d + 1), Y)) (U V : Set Y) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : ∀ x, b x ∈ U ∪ V)
    (hleft : ∀ x, b (Fin.cons 0 x) ∈ U) (hright : ∀ x, b (Fin.cons 1 x) ∈ V)
    (hboundary : ∀ t x, x ∈ _root_.Cube.boundary (Fin d) → b (Fin.cons t x) ∈ U ∩ V)
    (a₁ b₁ a₂ b₂ : unitInterval) (hab : a₁ < b₁) (hbc : b₁ ≤ a₂) (hce : a₂ < b₂)
    (p q : ℕ) (hd : d + 1 ≤ p + q)
    (hUV : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : U // y.val ∈ V}, U)) p)
    (hVU : IsHomotopyConnectedMap
      (⟨Subtype.val, continuous_subtype_val⟩ : C({y : V // y.val ∈ U}, V)) q) :
    ∃ v : C(Cube (d + 1), Y), ∃ H : b.Homotopy v,
      ∀ r x, x ∈ _root_.Cube.boundary (Fin d) →
        (⟨fun t ↦ H (r, Fin.cons t x), by fun_prop⟩ : C(unitInterval, Y)) =
          ⟨fun t ↦ b (Fin.cons t x), by fun_prop⟩ := by
  obtain ⟨v, H, _, _, hfix, _⟩ := exists_relative_two_chart_column_normalization d b U V
    hU hV hcover hleft hright hboundary a₁ b₁ a₂ b₂ hab hbc hce p q (by omega) hUV hVU
  exact ⟨v, H, fun r x hx ↦ ContinuousMap.ext (fun t ↦ hfix r t x hx)⟩

/-- The actual original cylinder path, with its source point and unchanged interval coordinate. -/
def originalCylinderCube {A D : TopCat.{u}} (l : A ⊗ TopCat.I ⟶ D) (a : A) :
    C(Cube 1, D) := ⟨fun x ↦ l (a, ULift.up (x 0)),
    l.hom.continuous.comp (by fun_prop)⟩

/-- A genuine original cylinder path can be normalized in the positive finite range, while
its two moving endpoints remain in their respective actual collars at every time. -/
theorem original_cylinder_finite_range {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (Quillen.intervalEndpoints A) (DoubleCylinder.endMap f g) l e)
    (lo hi : unitInterval) (hcut : lo < hi) (p q : ℕ) (hpq : 1 ≤ p + q)
    (hf : IsHomotopyConnectedMap f.hom p) (hg : IsHomotopyConnectedMap g.hom q)
    (a : A) (a₁ b₁ a₂ b₂ : unitInterval) (hab : a₁ < b₁) (hbc : b₁ ≤ a₂) (hce : a₂ < b₂) :
    ∃ v : C(Cube 1, D), ∃ H : (originalCylinderCube l a).Homotopy v,
      (∀ r, DoubleCylinder.height f g sq (H (r, fun _ ↦ 0)) < hi) ∧
      (∀ r, lo < DoubleCylinder.height f g sq (H (r, fun _ ↦ 1))) ∧
      ((∀ t, DoubleCylinder.height f g sq (v (fun _ ↦ t)) < hi) ∨
        ∀ t, lo < DoubleCylinder.height f g sq (v (fun _ ↦ t))) := by
  have hleft (x : Cube 0) :
      DoubleCylinder.height f g sq (originalCylinderCube l a (Fin.cons 0 x)) < hi := by
    change DoubleCylinder.height f g sq (l (a, ULift.up 0)) < hi
    rw [DoubleCylinder.height_cylinder]
    exact lt_of_le_of_lt (bot_le : 0 ≤ lo) hcut
  have hright (x : Cube 0) :
      lo < DoubleCylinder.height f g sq (originalCylinderCube l a (Fin.cons 1 x)) := by
    change lo < DoubleCylinder.height f g sq (l (a, ULift.up 1))
    rw [DoubleCylinder.height_cylinder]
    exact lt_of_lt_of_le hcut (le_top : hi ≤ 1)
  have hboundary (t : unitInterval) (x : Cube 0) (hx : x ∈ _root_.Cube.boundary (Fin 0)) :
      DoubleCylinder.height f g sq (originalCylinderCube l a (Fin.cons t x)) < hi ∧
        lo < DoubleCylinder.height f g sq (originalCylinderCube l a (Fin.cons t x)) := by
    obtain ⟨i, _⟩ := hx
    exact Fin.elim0 i
  obtain ⟨v, H, hHleft, hHright, _, hcolumn⟩ := DoubleCylinder.exists_relative_column_normalization
    f g sq lo hi hcut 0 p q (by omega) hf hg (originalCylinderCube l a)
    hleft hright hboundary a₁ b₁ a₂ b₂ hab hbc hce
  have he (t : unitInterval) : Fin.cons t (fun i : Fin 0 ↦ Fin.elim0 i) = fun _ : Fin 1 ↦ t := by
    funext i
    exact Fin.cases rfl (fun j ↦ Fin.elim0 j) i
  refine ⟨v, H, ?_, ?_, ?_⟩
  · intro r
    simpa only [he] using hHleft r (fun i ↦ Fin.elim0 i)
  · intro r
    simpa only [he] using hHright r (fun i ↦ Fin.elim0 i)
  · simpa only [he] using hcolumn (fun i ↦ Fin.elim0 i)

/-- The asymmetric component edge case genuinely uses only zero connectivity on g. -/
theorem original_zero_right_bound {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (Quillen.intervalEndpoints A) (DoubleCylinder.endMap f g) l e)
    (lo hi : unitInterval) (hcut : lo < hi)
    (hf : IsHomotopyConnectedMap f.hom 1) (hg : IsHomotopyConnectedMap g.hom 0)
    (a : A) (a₁ b₁ a₂ b₂ : unitInterval) (hab : a₁ < b₁) (hbc : b₁ ≤ a₂) (hce : a₂ < b₂) :
    ∃ v : C(Cube 1, D), ∃ H : (originalCylinderCube l a).Homotopy v,
      ∀ r, DoubleCylinder.height f g sq (H (r, fun _ ↦ 0)) < hi ∧
        lo < DoubleCylinder.height f g sq (H (r, fun _ ↦ 1)) := by
  obtain ⟨v, H, hleft, hright, _⟩ := original_cylinder_finite_range f g sq lo hi hcut 1 0
    (by omega) hf hg a a₁ b₁ a₂ b₂ hab hbc hce
  exact ⟨v, H, fun r ↦ ⟨hleft r, hright r⟩⟩

end QuillenTest.TwoChartGridNormalization
