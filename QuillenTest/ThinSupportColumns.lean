/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.CubicalSubdivision.ColumnAvoidance
public import Quillen.Topology.DoubleMappingCylinder.Collars

/-!
# Original vertical columns, including the actual double-cylinder height cover

The two offending times may differ, as may their vertical grid cells. The actual cylinder
consumer retains every map in its pushout square and expresses the finite range as
`d + 1 ≤ p + q`, with d the parameter dimension and d+1 the path cube dimension.
-/

@[expose] public section

open Quillen.CubicalSubdivision


noncomputable section

open CategoryTheory Limits MonoidalCategory
open scoped Topology unitInterval

universe u

namespace QuillenTest.ThinSupportColumns

open Quillen

open CubicalSubdivision

/-- The original path coordinate contributes at most one, even at two unrelated times. -/
theorem original_distinct_times_exclusion (d : ℕ) (a b c e : unitInterval) (hbc : b ≤ c)
    (p q : ℕ) (hd : d + 1 ≤ p + q) (x : Cube d) (s t : unitInterval)
    (hs : Fin.cons s x ∈ Quillen.Cube.thinSupport a b (p + 1)) :
    Fin.cons t x ∉ Quillen.Cube.thinSupport c e (q + 1) :=
  Quillen.Cube.column_not_mem_both a b c e hbc p q (by omega) x s t hs

/-- With no horizontal coordinates, support in two coordinates is impossible at any time.
This checks the case where one attaching connectivity is zero and the other is positive. -/
theorem original_zero_parameter_column (a b : unitInterval) (q : ℕ) (hq : 0 < q)
    (x : Cube 0) (t : unitInterval) :
    Fin.cons t x ∉ Quillen.Cube.thinSupport a b (q + 1) := by
  intro hx
  have h := Quillen.Cube.thinSupport_cons_imp a b t q x hx
  change q ≤ (Quillen.Cube.bandCoordinates a b x).card at h
  have he : Quillen.Cube.bandCoordinates a b x = ∅ := Finset.eq_empty_of_isEmpty _
  simp only [he, Finset.card_empty] at h
  omega

/-- After actual per-cell normalization, every original path in the original double mapping
cylinder lies in one of its actual height collars. No connectivity conclusion is assumed here. -/
theorem original_double_cylinder_columns
    {A B C D : TopCat.{u}} (f : A ⟶ B) (g : A ⟶ C)
    {l : A ⊗ TopCat.I ⟶ D} {e : TopCat.of (B ⊕ C) ⟶ D}
    (sq : IsPushout (Quillen.intervalEndpoints A) (DoubleCylinder.endMap f g) l e)
    (lo hi : unitInterval) (hcut : lo < hi)
    (d mesh p q : ℕ) (hd : d + 1 ≤ p + q)
    (a b c v : unitInterval) (hbc : b ≤ c) (F : C(Cube (d + 1), D))
    (hU : ∀ k, (F.comp (cell (d + 1) mesh k)) ⁻¹'
      (DoubleCylinder.leftCollarSet f g sq hi \ DoubleCylinder.rightCollarSet f g sq lo) ⊆
        Quillen.Cube.thinSupport a b (p + 1))
    (hV : ∀ k, (F.comp (cell (d + 1) mesh k)) ⁻¹'
      (DoubleCylinder.rightCollarSet f g sq lo \ DoubleCylinder.leftCollarSet f g sq hi) ⊆
        Quillen.Cube.thinSupport c v (q + 1)) (x : Cube d) :
    (∀ t, DoubleCylinder.height f g sq (F (Fin.cons t x)) < hi) ∨
      ∀ t, lo < DoubleCylinder.height f g sq (F (Fin.cons t x)) := by
  apply grid_column_image_subset_one d mesh a b c v hbc p q (by omega) F
    (DoubleCylinder.leftCollarSet f g sq hi) (DoubleCylinder.rightCollarSet f g sq lo) _ hU hV x
  intro z
  rw [DoubleCylinder.collar_cover f g sq hi lo hcut]
  trivial

end QuillenTest.ThinSupportColumns
