/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.Topology.Prespectrum.PushoutInterchangeIso

/-! Regression tests on original double cylinders and natural inverse interchange. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Quillen.LoopPrespectrum Quillen.LoopPrespectrum.HomotopyPushout
open scoped Topology unitInterval
universe u
variable {G G' : SpanGrid.{u}} (h : SpanGrid.Hom G G')

/-- Transport in the transposed grid and transport back preserve both original overlap times. -/
example (n : ℕ) (r s : unitInterval) (x : (G.obj 0 0).space n) :
    (G.interchangeIso.hom ≫ h.transpose.iteratedMap ≫ G'.interchangeIso.inv).map n
      (cylinder G.rowLeft G.rowRight n
        (r, cylinder (G.horizontalLeft 0) (G.horizontalRight 0) n (s, x))) =
      cylinder G'.rowLeft G'.rowRight n
        (r, cylinder (G'.horizontalLeft 0) (G'.horizontalRight 0) n
          (s, (h.app 0 0).map n x)) := rfl

/-- The natural inverse square holds on the entire original quotients. -/
example :
    G.interchangeIso.hom ≫ h.transpose.iteratedMap ≫ G'.interchangeIso.inv =
      h.iteratedMap := by
  change G.interchange ≫ h.transpose.iteratedMap ≫ G'.transpose.interchange = h.iteratedMap
  rw [← Category.assoc, ← h.interchange_naturality, Category.assoc,
    SpanGrid.interchange_comp_transpose, Category.comp_id]

/-- An overlap face is checked with the other overlap time still arbitrary. -/
example (n : ℕ) (s : unitInterval) (x : (G.obj 0 0).space n) :
    G.interchange.map n
      (cylinder G.rowLeft G.rowRight n
        (0, cylinder (G.horizontalLeft 0) (G.horizontalRight 0) n (s, x))) =
      cylinder G.transpose.rowLeft G.transpose.rowRight n
        (s, left (G.verticalLeft 0) (G.verticalRight 0) n ((G.verticalLeft 0).map n x)) := by
  rw [SpanGrid.interchange_cylinder_cylinder, cylinder_zero]

/-- The second overlap face likewise retains the first independent time. -/
example (n : ℕ) (r : unitInterval) (x : (G.obj 0 0).space n) :
    G.interchange.map n
      (cylinder G.rowLeft G.rowRight n
        (r, cylinder (G.horizontalLeft 0) (G.horizontalRight 0) n (1, x))) =
      right G.transpose.rowLeft G.transpose.rowRight n
        (cylinder (G.verticalLeft 2) (G.verticalRight 2) n
          (r, (G.horizontalRight 0).map n x)) := by
  rw [SpanGrid.interchange_cylinder_cylinder, cylinder_one]
  rfl

#print axioms SpanGrid.interchange
#print axioms SpanGrid.interchangeSquare
#print axioms SpanGrid.interchangeIso
#print axioms SpanGrid.interchange_comp_transpose
#print axioms SpanGrid.Hom.interchange_naturality
