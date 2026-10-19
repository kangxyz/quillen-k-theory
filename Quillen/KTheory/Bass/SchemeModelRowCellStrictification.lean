/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.ModelUnitRowCellStrictification
public import Quillen.KTheory.Bass.SchemeModelRowNormalizedBoundary

/-! # Returned-action strictification on the original scheme Bass squares

Every stage is formed by the unchanged cone and loop recursion from the specified
returned transformation. The original normalized forward is identified only after
that independent construction. Geometric provenance of the return data is separate.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace Quillen.KTheory.Bass.SchemeModelRowStrictification
open GeometricSeedCospan GeometricSquareInterchange ModelDiagramRowInterchange
variable (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)) ≅ 𝟭 (M.obj (laurent.op.obj X)))
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).functor (unit X) (unit Y))
  (R : ∀ X, M.obj X ⟶ M.obj (laurent.op.obj X))
  (e : ∀ X, (M.map (coefficient.app X)).functor ≅ (R X).functor)
  (μ : ∀ X, (R X).functor ⟶ (R X).functor)
  (he : ∀ X, (onFunctor (M.map (coefficient.app X)).functor (unit X)).hom ≫ (e X).hom =
    (e X).hom ≫ μ X)

/-- Iterate the actual returned-action cell on the original scheme squares. -/
def iteratedCell (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  (ModelUnitRowStrictification.iteratedFamily laurent.op coefficient M unit hunit R e μ he
    squareFunctor
    (interchange (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ))))
    (squareIso_projection (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ)))) i).val X

/-- The complete independently iterated cell agrees with the original cell at every stage. -/
theorem iteratedCell_eq (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    iteratedCell M unit hunit R e μ he i X = SchemeModelRowSeed.cell M unit hunit i X :=
  ModelUnitRowStrictification.iteratedCell_eq laurent.op coefficient M unit hunit R e μ he
    squareFunctor
    (interchange (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ))))
    (squareIso_projection (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentProjection
      (.of (ULift.{u} ℤ)))) i X

/-- Normalize each independently constructed returned-action cell before its original boundary. -/
def normalizedForward (i : ℕ) (X : Scheme.{u}ᵒᵖ) :=
  DiagramRowSeed.normalizedBoundary squareFunctor
    ((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor))
    (stage squareFunctor M i) (stage_point squareFunctor M i)
    (stage_naturality squareFunctor M i) (stage_structure squareFunctor M i) X
    (SchemeRowSeed.diagonalCell _ _ _ _ _ X (iteratedCell M unit hunit R e μ he i X))

/-- Original normalized forward maps are identified after the actual returned-action recursion. -/
theorem normalizedForward_eq (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    normalizedForward M unit hunit R e μ he i X =
      SchemeModelRowSeed.normalizedBoundary M unit hunit i X := by
  unfold normalizedForward
  rw [iteratedCell_eq]
  rfl

end Quillen.KTheory.Bass.SchemeModelRowStrictification
