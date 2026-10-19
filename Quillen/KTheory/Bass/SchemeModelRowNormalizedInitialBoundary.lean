/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeModelRowNormalizedBoundary
public import Quillen.KTheory.Bass.SchemeRowNormalizedBoundary

/-! # The initial independent row cell in the normalized boundary construction

This whole-map identification changes only the actual geometric diagonal endpoint witness.
It exposes the initial operation before concrete parameter Models are instantiated.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace Quillen.KTheory.Bass.SchemeModelRowSeed
open GeometricSeedCospan ModelDiagramRowInterchange
variable (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)) ≅ 𝟭 (M.obj (laurent.op.obj X)))
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).functor (unit X) (unit Y))

/-- Stage zero retains the independently realized initial cell and original Laurent inclusion. -/
theorem normalizedBoundary_zero (X : Scheme.{u}ᵒᵖ) :
    normalizedBoundary M unit hunit 0 X =
      RowRefinement.normalizedOperation (initial M (laurent.op.obj X))
        (initial_point M (laurent.op.obj X)) _
        (ModelDiagramRowInterchange.initialCell laurent.op coefficient M unit X) ≫
      parameterLoopingMap (DiagramRowSeed.inclusion squareFunctor (M ⋙ prespectrumFunctor)
        (initial M) (initial_point M) (initial_naturality M) X) := by
  exact SchemeRowSeed.normalizedBoundary_diagonalCell
    ((strictDiagramIterate squareFunctor 0).obj (M ⋙ prespectrumFunctor))
    (stage squareFunctor M 0) (stage_point squareFunctor M 0)
    (stage_naturality squareFunctor M 0) (stage_structure squareFunctor M 0)
    X (cell M unit hunit 0 X)

end Quillen.KTheory.Bass.SchemeModelRowSeed
