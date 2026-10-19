/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeRowSeed
public import Quillen.KTheory.Bass.DiagramRowNormalizedBoundary

/-! # Original diagonal witnesses in the normalized geometric boundary

Changing the endpoint witness of the independent cell leaves its whole normalized operation
unchanged. This identifies the actual geometric diagonal before specializing any Model stage.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Quillen.LoopPrespectrum
open scoped Topology unitInterval
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace Quillen.LoopPrespectrum.RowRefinement

/-- Inverse-prefix normalization retains a self-track under an endpoint equality cast. -/
theorem normalizedOperation_cast {D E : LoopPrespectrum.{w}}
    (q : ∀ k, C(E.space (k + 3), E.space (k + 3)))
    (hp : ∀ k, q k (E.point (k + 3)) = E.point (k + 3))
    {f g : D ⟶ spectrum E q hp} (H : Homotopy f f) (h : f = g) :
    normalizedOperation q hp g (H.cast h h) = normalizedOperation q hp f H := by
  subst g
  rfl

end Quillen.LoopPrespectrum.RowRefinement

namespace Quillen.KTheory.Bass.SchemeRowSeed
open GeometricSeedCospan
variable (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
  (q : ∀ X k, C((F.obj X).space (k + 3), (F.obj X).space (k + 3)))
  (hp : ∀ X k, q X k ((F.obj X).point (k + 3)) = (F.obj X).point (k + 3))
  (hn : ∀ {X Y} (g : X ⟶ Y) k x,
    q Y k ((F.map g).map (k + 3) x) = (F.map g).map (k + 3) (q X k x))
  (hs : ∀ X k (x : (F.obj X).space (k + 1)) (s t : unitInterval),
    q X k ((F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x s) t) =
      (F.obj X).structureMap (k + 2) ((F.obj X).structureMap (k + 1) x t) s)

/-- The geometric diagonal cast preserves the independent normalized cup and original inclusion.
-/
theorem normalizedBoundary_diagonalCell (X : Scheme.{u}ᵒᵖ)
    (K : Homotopy ((DiagramRowCell.input laurent.op coefficient F q hp hn hs).app X)
      ((DiagramRowCell.input laurent.op coefficient F q hp hn hs).app X)) :
    DiagramRowSeed.normalizedBoundary squareFunctor F q hp hn hs X
        (diagonalCell F q hp hn hs X K) =
      RowRefinement.normalizedOperation (q (laurent.op.obj X)) (hp (laurent.op.obj X)) _ K ≫
        parameterLoopingMap (DiagramRowSeed.inclusion squareFunctor F q hp hn X) := by
  exact congrArg
    (fun a : F.obj X ⟶ parameterLooping
        (RowRefinement.spectrum (F.obj (laurent.op.obj X))
          (q (laurent.op.obj X)) (hp (laurent.op.obj X))) =>
      a ≫ parameterLoopingMap (DiagramRowSeed.inclusion squareFunctor F q hp hn X))
    (RowRefinement.normalizedOperation_cast (q (laurent.op.obj X))
      (hp (laurent.op.obj X)) K
      (show (DiagramRowCell.input laurent.op coefficient F q hp hn hs).app X =
        DiagramRowSeed.diagonal squareFunctor F X ≫
          DiagramRowSeed.cornerComparison squareFunctor F q hp hs X by
        rw [diagonal_eq]
        rfl))

end Quillen.KTheory.Bass.SchemeRowSeed
