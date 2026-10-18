/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.GeometricSeedCospan

/-!
# Regression for the finite whole geometric seed cospan

These consumers retain the actual source identity, original unit clock, full
source-null family, and actual map equality. There is no extra unit-square or
whole-seed input beyond the original natural track.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen Quillen.LoopPrespectrum
open Quillen.KTheory.Bass
open GeometricSquareInterchange GeometricSeedCospan
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace QuillenTest.WholeGeometricSeedCospan
variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (H : ∀ X, Homotopy (F.map (coefficient.app X)) (F.map (coefficient.app X)))
    (hH : ∀ {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r : unitInterval)
      (x : (F.obj X).space n),
      (F.map (laurent.op.map g)).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (F.map g).map n x))

/-- The original unit time is unchanged by the exact diagonal endpoint cast. -/
theorem source_clock (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r : unitInterval)
    (x : (F.obj X).space n) :
    (sourceTrack F H X).level n (r,x) = (H X).level n (r,x) := rfl

/-- The common-target comparison uses the actual identity on the original base corner. -/
theorem source_identity : (squareInterchangeMap F).left.left =
    𝟙 ((strictDiagramFunctor squareFunctor).obj F) := squareInterchange_base F

/-- The whole current-stage unit square is obtained from the original natural track alone. -/
theorem actual_unit_square (X : Scheme.{u}ᵒᵖ) (r : unitInterval) :
    (bassTrack F H hH X).at r ≫ (squareInterchangeMap F).right.right.app X =
      (strictDiagramMapHomotopy (sourceTrack F H) (sourceTrack_naturality F H hH)
        squareFunctor X).at r := wholeUnitSquare F H hH X r

#print axioms HomotopyWord.map_trans
#print axioms WholeSeedCospan.chiAlong_sourceNull
#print axioms WholeSeedCospan.chiAlong_word
#print axioms WholeSeedCospan.seed_cospan
#print axioms GeometricSquareInterchange.squareInterchangeMap
#print axioms GeometricSeedCospan.wholeUnitSquare
#print axioms GeometricSeedCospan.chiGeom_sourceNull
#print axioms GeometricSeedCospan.seed_cospan

end QuillenTest.WholeGeometricSeedCospan
