/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.DiagramRowSeed
public import Quillen.KTheory.Bass.DiagramRowCellCone
public import Quillen.KTheory.Bass.SchemeNaturalSeed

/-!
# Independent row seeds on the original scheme Laurent square

Only the actual geometric diagonal identity changes the endpoint witnesses.
The independent cell and original source null determine the refined seed.
A whole-cell comparison identifies its actual map with the original seed
followed by the parameter-looped cone row comparison.
-/
@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u w
namespace Quillen.KTheory.Bass.SchemeRowSeed
open GeometricSeedCospan NaturalTrack GeometricSquareInterchange
variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
  (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
    q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
      (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)

/-- The geometric square's original diagonal is the specified Laurent coefficient. -/
theorem diagonal_eq (X : Scheme.{u}ᵒᵖ) :
    DiagramRowSeed.diagonal squareFunctor F X = F.map (coefficient.app X) :=
  congrArg (fun a => a.app X) (geometricSquare_diagonal F)

/-- Only endpoint witnesses change when the original cell is used on the geometric square. -/
def diagonalCell (X : Scheme.{u}ᵒᵖ)
    (K : Homotopy ((DiagramRowCell.input laurent.op coefficient F q hp hn hs).app X)
      ((DiagramRowCell.input laurent.op coefficient F q hp hn hs).app X)) :
    Homotopy
      (DiagramRowSeed.diagonal squareFunctor F X ≫
        DiagramRowSeed.cornerComparison squareFunctor F q hp hs X)
      (DiagramRowSeed.diagonal squareFunctor F X ≫
        DiagramRowSeed.cornerComparison squareFunctor F q hp hs X) :=
  K.cast (by rw [diagonal_eq]; rfl) (by rw [diagonal_eq]; rfl)

/-- The genuine refined seed is formed from the independent cell and original whole cone null. -/
def seed (X : Scheme.{u}ᵒᵖ)
    (K : Homotopy ((DiagramRowCell.input laurent.op coefficient F q hp hn hs).app X)
      ((DiagramRowCell.input laurent.op coefficient F q hp hn hs).app X)) :
    F.obj X ⟶ parameterLooping (DiagramRowSeed.carrier squareFunctor F q hp hn X) :=
  DiagramRowSeed.seed squareFunctor F q hp hn hs X (diagonalCell F q hp hn hs X K)

/-- An independently proved whole-cell equality identifies the original map, not only classes. -/
theorem seed_eq (A : Track laurent.op coefficient F) (X : Scheme.{u}ᵒᵖ)
    (K : Homotopy ((DiagramRowCell.input laurent.op coefficient F q hp hn hs).app X)
      ((DiagramRowCell.input laurent.op coefficient F q hp hn hs).app X))
    (hK : K = (A.homotopy X).postcomp
      ((DiagramRowRefinement.comparison F q hp hn hs).app (laurent.op.obj X))) :
    seed F q hp hn hs X K = (SchemeNaturalSeed.seed A).app X ≫
      parameterLoopingMap (DiagramRowSeed.comparison squareFunctor F q hp hn hs X) := by
  apply DiagramRowSeed.seed_eq
  subst K
  apply Homotopy.ext
  rfl

end Quillen.KTheory.Bass.SchemeRowSeed
