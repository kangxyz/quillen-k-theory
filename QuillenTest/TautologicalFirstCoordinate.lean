/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.ProjectiveLine.TautologicalFirstCoordinate
public import Mathlib.Data.ZMod.Basic

/-! Both actual trivialized first-coordinate maps, including the empty zero-ring chart. -/
set_option autoImplicit false
set_option linter.mathlibStandardSet true
set_option warningAsError true

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.ProjectiveLine
  AlgebraicGeometry.Scheme.Modules
universe u
namespace QuillenTest.TautologicalFirstCoordinate

/-- Conjugating the positive restriction by the actual chart isomorphisms gives the identity. -/
theorem positive_coordinate_identity (R : CommRingCat.{u}) :
    (tautologicalLinePlusIso R).inv ≫
      (Scheme.Modules.restrictFunctor (plusChart R)).map (tautologicalInclusionFirstProjection R) ≫
        (Scheme.Modules.restrictUnitIso (plusChart R)).hom = 𝟙 _ := by
  rw [tautologicalInclusionFirstProjection_plus]
  simp

/-- Conjugating the negative restriction gives the original scalar, with its original sign. -/
private theorem negative_coordinate_scalar (R : CommRingCat.{u}) :
    (tautologicalLineMinusIso R).inv ≫
      (Scheme.Modules.restrictFunctor (minusChart R)).map (tautologicalInclusionFirstProjection R) ≫
        (Scheme.Modules.restrictUnitIso (minusChart R)).hom =
      unitMul _ (polynomialCoordinate R) := by
  rw [tautologicalInclusionFirstProjection_minus]
  simp

/-- The positive restriction remains an isomorphism over the zero ring. -/
private theorem zero_ring_positive_coordinate_isIso :
    IsIso ((Scheme.Modules.restrictFunctor (plusChart (.of (ZMod 1)))).map
      (tautologicalInclusionFirstProjection (.of (ZMod 1)))) :=
  tautologicalInclusionFirstProjection_plus_isIso _

end QuillenTest.TautologicalFirstCoordinate
