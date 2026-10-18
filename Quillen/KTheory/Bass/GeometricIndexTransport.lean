/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.IndexSquareFactor
public import Quillen.KTheory.Bass.SquareConeStrength

/-!
# Actual geometric Bass factor transports

The four original integer-base swaps give a natural square isomorphism between
applying the geometric square after Bass and applying Bass to the original
square. Its edges use the proved factor projection and positive/inverse charts.
No unit-track or seed compatibility is assumed here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Products
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.LoopPrespectrum
universe u w u₁ v₁
namespace Quillen.KTheory.Bass.GeometricSquareInterchange
variable {T T' : Scheme.{u}} (q : T ⟶ integerBase) (q' : T' ⟶ integerBase)
  (f : T ⟶ T') (hf : f ≫ q' = q) (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})

/-- The original four-corner cone/loop image of index interchange. -/
def eta : (baseProductFunctor q).op ⋙ (strictDiagramFunctor squareFunctor).obj F ≅
    (strictDiagramFunctor squareFunctor).obj ((baseProductFunctor q).op ⋙ F) :=
  Functor.isoWhiskerRight (interchange q) (F.mapArrow.mapArrow ⋙ strictSquareLoopedConeFunctor)

/-- Its components retain the actual four original swaps. -/
theorem eta_hom_app (X : Scheme.{u}ᵒᵖ) :
    (eta q F).hom.app X = strictSquareLoopedConeFunctor.map
      (F.mapArrow.mapArrow.map (squareIso q X).hom) := rfl

/-- Naturality in the independent factor retains the actual factor map. -/
theorem eta_factor :
    Functor.whiskerRight (NatTrans.op (baseProductTransformation q q' f hf))
        ((strictDiagramFunctor squareFunctor).obj F) ≫ (eta q F).hom =
      (eta q' F).hom ≫ (strictDiagramFunctor squareFunctor).map
        (Functor.whiskerRight (NatTrans.op (baseProductTransformation q q' f hf)) F) := by
  apply NatTrans.ext
  funext X
  let K := F.mapArrow.mapArrow ⋙ strictSquareLoopedConeFunctor
  change K.map (squareFunctor.map ((baseProductTransformation q q' f hf).app X.unop).op) ≫
      K.map (squareIso q X).hom = K.map (squareIso q' X).hom ≫
        K.map (onSquare (NatTrans.op (baseProductTransformation q q' f hf)) (square X))
  rw [← K.map_comp, ← K.map_comp, squareIso_factor]

/-- The source projection is preserved by the original factor interchange. -/
theorem eta_projection :
    Functor.whiskerRight (NatTrans.op (baseProductProjection q))
        ((strictDiagramFunctor squareFunctor).obj F) ≫ (eta q F).hom =
      (strictDiagramFunctor squareFunctor).map
        (Functor.whiskerRight (NatTrans.op (baseProductProjection q)) F) := by
  apply NatTrans.ext
  funext X
  let K := F.mapArrow.mapArrow ⋙ strictSquareLoopedConeFunctor
  change K.map (squareFunctor.map ((baseProductProjection q).app X.unop).op) ≫
      K.map (squareIso q X).hom =
        K.map (onSquare (NatTrans.op (baseProductProjection q)) (square X))
  rw [← K.map_comp, squareIso_projection]

/-- The original polynomial projection applied by the actual spectrum diagram. -/
def projectionMap : F ⟶ polynomial.op ⋙ F :=
  Functor.whiskerRight (NatTrans.op projection) F

/-- The original positive chart applied by the actual spectrum diagram. -/
def plusMap : polynomial.op ⋙ F ⟶ laurent.op ⋙ F :=
  Functor.whiskerRight (NatTrans.op plus) F

/-- The original inverse chart applied by the actual spectrum diagram. -/
def minusMap : polynomial.op ⋙ F ⟶ laurent.op ⋙ F :=
  Functor.whiskerRight (NatTrans.op minus) F

/-- The original charts have the same original spectrum-level composite. -/
theorem chartMap_projection :
    projectionMap F ≫ plusMap F = projectionMap F ≫ minusMap F := by
  apply NatTrans.ext
  funext X
  change F.map (projection.app X.unop).op ≫ F.map (plus.app X.unop).op =
    F.map (projection.app X.unop).op ≫ F.map (minus.app X.unop).op
  rw [← F.map_comp, ← F.map_comp]
  exact congrArg F.map (Quiver.Hom.unop_inj (chart_projection X.unop))

/-- Collect the unchanged geometric maps into a square with its source literally F. -/
def geometricSquare : Arrow (Arrow (Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})) :=
  Arrow.mk (Arrow.homMk (f := Arrow.mk (projectionMap F))
    (g := Arrow.mk (minusMap F)) (projectionMap F) (plusMap F)
    (chartMap_projection F).symm)

/-- Every component is the original geometric square, with all four original maps. -/
theorem geometricSquare_component (X : Scheme.{u}ᵒᵖ) :
    (SquareConeStrength.squareDiagram (geometricSquare F)).obj X =
      F.mapArrow.mapArrow.obj (square X) := rfl

/-- The polynomial source equation in the literal source functors used by the square. -/
theorem projectionMap_eta :
    projectionMap ((strictDiagramFunctor squareFunctor).obj F) ≫
        (eta (polynomialProjection (.of (ULift.{u} ℤ))) F).hom =
      (strictDiagramFunctor squareFunctor).map (projectionMap F) := by
  apply NatTrans.ext
  funext X
  exact congrArg (fun k => k.app X)
    (eta_projection (polynomialProjection (.of (ULift.{u} ℤ))) F)

/-- Remove only the literal identity from a specified compositional equation. -/
theorem id_comp_of_comp_eq {D : Type u₁} [Category.{v₁} D]
    {X Y Z : D} {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z} (h : f ≫ g = k) :
    𝟙 X ≫ k = f ≫ g := (Category.id_comp k).trans h.symm

/-- The original diagonal is exactly the original Laurent projection. -/
theorem geometricSquare_diagonal :
    (geometricSquare F).left.hom ≫ (geometricSquare F).hom.right =
      Functor.whiskerRight (NatTrans.op
        (baseProductProjection (laurentProjection (.of (ULift.{u} ℤ))))) F := by
  apply NatTrans.ext
  funext X
  change F.map (projection.app X.unop).op ≫ F.map (plus.app X.unop).op = _
  rw [← F.map_comp]
  apply congrArg F.map
  apply Quiver.Hom.unop_inj
  exact baseProductTransformation_projection
    (laurentProjection (.of (ULift.{u} ℤ))) (polynomialProjection (.of (ULift.{u} ℤ)))
    (laurentPlus (.of (ULift.{u} ℤ))) (laurentPlus_projection (.of (ULift.{u} ℤ))) X.unop

end Quillen.KTheory.Bass.GeometricSquareInterchange
