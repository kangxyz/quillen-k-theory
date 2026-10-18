/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ConeTrack
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IndexSquareFactor

/-!
# Cone-track regression on the actual arbitrary-scheme index square

The factor projection and four original variable swaps, including both charts, discharge
all index hypotheses of the generic cone-track consumer. The original null cylinder keeps
its independent cone and action coordinates. No affine or Under-category replacement is used.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.KTheory.Bass
open scoped unitInterval
universe u w
namespace QuillenTest.ConeTrackScheme
variable {T : Scheme.{u}} (q : T ⟶ integerBase)
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (H : ∀ X : Scheme.{u}ᵒᵖ,
      Homotopy (F.map ((NatTrans.op (baseProductProjection q)).app X))
        (F.map ((NatTrans.op (baseProductProjection q)).app X)))
    (hH : ∀ {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r : unitInterval)
      (x : (F.obj X).space n),
      (F.map ((baseProductFunctor q).op.map g)).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (F.map g).map n x))

/-- The actual four-corner scheme interchange supplies the original cone coefficient track. -/
def action (X : Scheme.{u}ᵒᵖ) :
    Homotopy ((ConeTrack.diagram squareFunctor F).map
      ((baseProductProjection q).app X.unop).op)
      ((ConeTrack.diagram squareFunctor F).map
        ((baseProductProjection q).app X.unop).op) :=
  ConeTrack.action squareFunctor (baseProductFunctor q).op
    (NatTrans.op (baseProductProjection q)) (interchange q) (squareIso_projection q)
    F H hH X

/-- The derived genuine scheme action is natural for every scheme morphism and action time. -/
theorem action_naturality {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r : unitInterval)
    (x : ((ConeTrack.diagram squareFunctor F).obj X).space n) :
    ((ConeTrack.diagram squareFunctor F).map
      ((baseProductFunctor q).op.map g)).map n ((action q F H hH X).level n (r, x)) =
      (action q F H hH Y).level n
        (r, ((ConeTrack.diagram squareFunctor F).map g).map n x) :=
  ConeTrack.action_naturality squareFunctor (baseProductFunctor q).op
    (NatTrans.op (baseProductProjection q)) (interchange q) (squareIso_projection q)
    F H hH g n r x

/-- The actual fixed source corner removes the inverse-swap map without changing either time. -/
theorem action_sourceNull (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r s : unitInterval)
    (x : (F.obj X).space n) :
    (action q F H hH X).level n
      (r, (StrictSquare.sourceNullHomotopy (F.mapArrow.mapArrow.obj (square X))).level n
        (s, x)) =
      (StrictSquare.sourceNullHomotopy
        (F.mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X)))).level n
          (s, (H X).level n (r, x)) := by
  have h := ConeTrack.action_sourceNull squareFunctor (baseProductFunctor q).op
    (NatTrans.op (baseProductProjection q)) (interchange q) (squareIso_projection q)
    F H hH X n r s x
  change _ = (StrictSquare.sourceNullHomotopy
    (F.mapArrow.mapArrow.obj (square ((baseProductFunctor q).op.obj X)))).level n
      (s, (F.map (𝟙 ((baseProductFunctor q).op.obj X))).map n ((H X).level n (r, x))) at h
  rw [F.map_id] at h
  exact h

#print axioms Quillen.KTheory.Bass.ConeTrack.action
#print axioms Quillen.KTheory.Bass.ConeTrack.action_naturality
#print axioms Quillen.KTheory.Bass.ConeTrack.action_sourceNull
#print axioms QuillenTest.ConeTrackScheme.action_sourceNull

end QuillenTest.ConeTrackScheme
