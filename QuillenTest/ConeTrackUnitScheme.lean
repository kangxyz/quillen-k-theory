/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ConeTrackUnitSquare
public import Quillen.KTheory.Bass.GeometricIndexTransport

/-!
# The induced unit square with the actual geometric eta

The independently constructed arbitrary-scheme eta is the forward map inverse to
the index map in the specified cone-derived action. This regression retains the
original action time and input-loop time, and adds no scalar interchange assumption.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.KTheory.Bass
open scoped unitInterval
universe u w
namespace QuillenTest.ConeTrackUnitScheme
variable {T : Scheme.{u}} (q : T ⟶ integerBase)
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (H : ∀ X : Scheme.{u}ᵒᵖ,
      Homotopy (F.map ((NatTrans.op (baseProductProjection q)).app X))
        (F.map ((NatTrans.op (baseProductProjection q)).app X)))
    (hH : ∀ {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) (n : ℕ) (r : unitInterval)
      (x : (F.obj X).space n),
      (F.map ((baseProductFunctor q).op.map g)).map n ((H X).level n (r, x)) =
        (H Y).level n (r, (F.map g).map n x))

/-- The specified induced action satisfies the unit square with the original geometric eta. -/
theorem whole_unit_square (X : Scheme.{u}ᵒᵖ) (r : unitInterval) :
    (ConeTrack.action squareFunctor (baseProductFunctor q).op
      (NatTrans.op (baseProductProjection q)) (interchange q) (squareIso_projection q)
      F H hH X).parameterLooping.at r ≫
        (GeometricSquareInterchange.eta q F).hom.app X =
      (strictDiagramMapHomotopy
        (η := Functor.whiskerRight (NatTrans.op (baseProductProjection q)) F)
        (θ := Functor.whiskerRight (NatTrans.op (baseProductProjection q)) F)
        H hH squareFunctor X).at r :=
  ConeTrack.looped_action_index squareFunctor (baseProductFunctor q).op
    (NatTrans.op (baseProductProjection q)) (interchange q) (squareIso_projection q)
    F H hH X r

/-- The actual eta square leaves both action and input-loop coordinates untouched. -/
theorem whole_unit_square_apply (X : Scheme.{u}ᵒᵖ) (n : ℕ) (r t : unitInterval)
    (γ : Path (((ConeTrack.diagram squareFunctor F).obj X).point n)
      (((ConeTrack.diagram squareFunctor F).obj X).point n)) :
    Path.toContinuousMap
      (((GeometricSquareInterchange.eta q F).hom.app X).map n
        ((ConeTrack.action squareFunctor (baseProductFunctor q).op
          (NatTrans.op (baseProductProjection q)) (interchange q) (squareIso_projection q)
          F H hH X).parameterLooping.level n (r, γ))) t =
      (diagramSquareMapHomotopy
        (η := Functor.whiskerRight (NatTrans.op (baseProductProjection q)) F)
        (θ := Functor.whiskerRight (NatTrans.op (baseProductProjection q)) F)
        H hH (square X)).cone.level n (r, γ t) :=
  ConeTrack.looped_action_index_apply squareFunctor (baseProductFunctor q).op
    (NatTrans.op (baseProductProjection q)) (interchange q) (squareIso_projection q)
    F H hH X n r t γ

#print axioms Quillen.KTheory.Bass.ConeTrack.looped_action_index
#print axioms QuillenTest.ConeTrackUnitScheme.whole_unit_square
#print axioms QuillenTest.ConeTrackUnitScheme.whole_unit_square_apply

end QuillenTest.ConeTrackUnitScheme
