/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeModelRowSeed
public import Quillen.KTheory.Bass.DiagramRowNormalizedBoundary

/-!
# The normalized independent Model-unit cell followed by the original boundary

At every Bass stage the source operation is formed by the original inverse-prefix
normalization of the recursively constructed cell, before applying the Laurent cone
inclusion. Its comparison with the proper-row forward seed is a whole spectrum homotopy
using the original cone null. The initial tensor qualification is supplied separately by
the actual parameter tensor/evaluation prism; no full multiplicative structure is asserted.
-/
@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u w
namespace Quillen.KTheory.Bass.SchemeModelRowSeed
open GeometricSeedCospan NaturalTrack GeometricSquareInterchange ModelDiagramRowInterchange
variable (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)) ≅ 𝟭 (M.obj (laurent.op.obj X)))
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).functor (unit X) (unit Y))


/-- Normalize the genuine independently iterated cell before the actual boundary inclusion. -/
def normalizedBoundary (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    (((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor)).obj X) ⟶
      ModelDiagramRowStabilizedTarget.target squareFunctor i M X :=
  DiagramRowSeed.normalizedBoundary squareFunctor
    ((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor))
    (stage squareFunctor M i) (stage_point squareFunctor M i)
    (stage_naturality squareFunctor M i) (stage_structure squareFunctor M i) X
    (SchemeRowSeed.diagonalCell _ _ _ _ _ X (cell M unit hunit i X))

/-- The original normalization prism identifies the entire forward leg in the common row target.
-/
def normalizedBoundaryHomotopy (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    Homotopy (normalizedBoundary M unit hunit i X) (forward M unit hunit i X) :=
  DiagramRowSeed.normalizedBoundaryHomotopy squareFunctor
    ((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor))
    (stage squareFunctor M i) (stage_point squareFunctor M i)
    (stage_naturality squareFunctor M i) (stage_structure squareFunctor M i) X
    (SchemeRowSeed.diagonalCell _ _ _ _ _ X (cell M unit hunit i X))

/-- The independently normalized boundary leg has the actual current-transition factorization.
-/
def normalizedBoundaryCurrentHomotopy (i : ℕ) (X : Scheme.{u}ᵒᵖ) :
    Homotopy (normalizedBoundary M unit hunit i X)
      ((SchemeNaturalSeed.currentTransition
        (ofModelUnits laurent.op coefficient M unit hunit) i).app X ≫
        ModelRowZigzagSequentialization.backward squareFunctor M X i) :=
  (normalizedBoundaryHomotopy M unit hunit i X).cast rfl
    (forward_eq_current M unit hunit i X)

end Quillen.KTheory.Bass.SchemeModelRowSeed
