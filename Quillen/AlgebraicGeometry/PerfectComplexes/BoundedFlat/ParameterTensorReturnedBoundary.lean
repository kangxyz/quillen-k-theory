/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedCell
public import Quillen.KTheory.Bass.DiagramRowNormalizedBoundary
public import Quillen.KTheory.Bass.SchemeRowSeed
public import Quillen.Topology.Prespectrum.RowNormalizationPasting

/-!
# The original boundary and null for the returned genuine tensor cell

Returning through the actual evaluation inverse puts both endpoints in the original
parameter Model. Its original Laurent inclusion and original source null now apply.
The endpoint path transports that same null; inverse-prefix normalization retains the
entire first-row prism in this actual common target.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.KTheory.Bass
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex GeometricSeedCospan ModelDiagramRowInterchange

/-- The actual original ambient parameter spectrum diagram. -/
abbrev initialDiagram (Q : Scheme.{u}) := ParameterModels.ambient Q ⋙ prespectrumFunctor

/-- The original Laurent cone inclusion on the genuine row refinement. -/
def originalRowInclusion (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  DiagramRowSeed.inclusion squareFunctor (initialDiagram Q)
    (initial (ParameterModels.ambient Q)) (initial_point (ParameterModels.ambient Q))
    (initial_naturality (ParameterModels.ambient Q)) X

/-- The internal endpoint after the original refined Laurent inclusion. -/
def originalBoundaryEndpoint (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  (((initialDiagram Q).map (coefficient.app X)) ≫
    DiagramRowSeed.cornerComparison squareFunctor (initialDiagram Q)
      (initial (ParameterModels.ambient Q))
      (initial_point (ParameterModels.ambient Q))
      (initial_structure (ParameterModels.ambient Q)) X) ≫
        originalRowInclusion Q X

/-- The original geometric index square has the unchanged source parameter. -/
theorem originalSquareSource (X : Scheme.{u}ᵒᵖ) :
    (squareFunctor.obj X).left.left = X := rfl

/-- The unchanged original source null, with only the geometric diagonal witness adjusted. -/
def originalBoundaryNull (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    Homotopy (originalBoundaryEndpoint Q X) (zeroHom _ _) := by
  have h := DiagramRowSeed.includedNull squareFunctor (initialDiagram Q)
    (initial (ParameterModels.ambient Q)) (initial_point (ParameterModels.ambient Q))
    (initial_naturality (ParameterModels.ambient Q))
    (initial_structure (ParameterModels.ambient Q)) X
  simpa only [SchemeRowSeed.diagonal_eq, originalBoundaryEndpoint, originalRowInclusion,
    originalSquareSource, Functor.id_obj] using h

/-- The actual endpoint movement remains in the original cone's row carrier. -/
def returnedBoundaryMovement (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  (returnedMovement Q X).postcomp (originalRowInclusion Q X)

/-- The independently realized returned tensor cell is sent through the original inclusion. -/
def returnedBoundaryCell (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  (returnedTensorCell Q X).postcomp (originalRowInclusion Q X)

/-- The complete first-row prism survives the original boundary map. -/
def returnedBoundaryPasting (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (((initialCell Q X).postcomp (originalRowInclusion Q X)).trans
      (returnedBoundaryMovement Q X)).RelHomotopy
      ((returnedBoundaryMovement Q X).trans (returnedBoundaryCell Q X)) := by
  simpa only [Homotopy.postcomp_trans, returnedBoundaryMovement, returnedBoundaryCell] using
    (returnedPasting Q X).postcomp (originalRowInclusion Q X)

/-- The original null is transported along the actual evaluation/unitor endpoint path. -/
def returnedBoundaryNull (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  (returnedBoundaryMovement Q X).symm.trans (originalBoundaryNull Q X)

/-- Whole inverse-prefix normalization keeps the moving tensor prism and original null. -/
def returnedBoundaryNormalization (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :=
  RowRefinement.normalizationPasting
    (DiagramRowInterchange.cone squareFunctor (initialDiagram Q)
      (initial (ParameterModels.ambient Q)) (initial_point (ParameterModels.ambient Q))
      (initial_naturality (ParameterModels.ambient Q)) X)
    (DiagramRowInterchange.cone_point squareFunctor (initialDiagram Q)
      (initial (ParameterModels.ambient Q)) (initial_point (ParameterModels.ambient Q))
      (initial_naturality (ParameterModels.ambient Q)) X)
    (returnedBoundaryMovement Q X)
    ((initialCell Q X).postcomp (originalRowInclusion Q X))
    (returnedBoundaryCell Q X) (returnedBoundaryPasting Q X) (originalBoundaryNull Q X)

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
