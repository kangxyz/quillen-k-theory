/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorSupportedReturnedCell
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
namespace Quillen.PerfectComplexes.ParameterTensorSupportedRow
open GlobalSectionChangeIndex GeometricSeedCospan ModelDiagramRowInterchange
variable {P Q : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- The actual original supported parameter spectrum diagram. -/
abbrev initialDiagram := ParameterModels.supported f ⋙ prespectrumFunctor

/-- The original Laurent cone inclusion on the genuine row refinement. -/
def originalRowInclusion (X : Scheme.{u}ᵒᵖ) :=
  DiagramRowSeed.inclusion squareFunctor (initialDiagram f)
    (initial (ParameterModels.supported f)) (initial_point (ParameterModels.supported f))
    (initial_naturality (ParameterModels.supported f)) X

/-- The internal endpoint after the original refined Laurent inclusion. -/
def originalBoundaryEndpoint (X : Scheme.{u}ᵒᵖ) :=
  (((initialDiagram f).map (coefficient.app X)) ≫
    DiagramRowSeed.cornerComparison squareFunctor (initialDiagram f)
      (initial (ParameterModels.supported f))
      (initial_point (ParameterModels.supported f))
      (initial_structure (ParameterModels.supported f)) X) ≫
        originalRowInclusion f X

/-- The original geometric index square has the unchanged source parameter. -/
theorem originalSquareSource (X : Scheme.{u}ᵒᵖ) :
    (squareFunctor.obj X).left.left = X := rfl

/-- The unchanged original source null, with only the geometric diagonal witness adjusted. -/
def originalBoundaryNull (X : Scheme.{u}ᵒᵖ) :
    Homotopy (originalBoundaryEndpoint f X) (zeroHom _ _) := by
  have h := DiagramRowSeed.includedNull squareFunctor (initialDiagram f)
    (initial (ParameterModels.supported f)) (initial_point (ParameterModels.supported f))
    (initial_naturality (ParameterModels.supported f))
    (initial_structure (ParameterModels.supported f)) X
  simpa only [SchemeRowSeed.diagonal_eq, originalBoundaryEndpoint, originalRowInclusion,
    originalSquareSource, Functor.id_obj] using h

/-- The actual endpoint movement remains in the original cone's row carrier. -/
def returnedBoundaryMovement (X : Scheme.{u}ᵒᵖ) :=
  (returnedMovement f X).postcomp (originalRowInclusion f X)

/-- The independently realized returned tensor cell is sent through the original inclusion. -/
def returnedBoundaryCell (X : Scheme.{u}ᵒᵖ) :=
  (returnedTensorCell f X).postcomp (originalRowInclusion f X)

/-- The complete first-row prism survives the original boundary map. -/
def returnedBoundaryPasting (X : Scheme.{u}ᵒᵖ) :
    (((initialCell f X).postcomp (originalRowInclusion f X)).trans
      (returnedBoundaryMovement f X)).RelHomotopy
      ((returnedBoundaryMovement f X).trans (returnedBoundaryCell f X)) := by
  simpa only [Homotopy.postcomp_trans, returnedBoundaryMovement, returnedBoundaryCell] using
    (returnedPasting f X).postcomp (originalRowInclusion f X)

/-- The original null is transported along the actual evaluation/unitor endpoint path. -/
def returnedBoundaryNull (X : Scheme.{u}ᵒᵖ) :=
  (returnedBoundaryMovement f X).symm.trans (originalBoundaryNull f X)

/-- Whole inverse-prefix normalization keeps the moving tensor prism and original null. -/
def returnedBoundaryNormalization (X : Scheme.{u}ᵒᵖ) :=
  RowRefinement.normalizationPasting
    (DiagramRowInterchange.cone squareFunctor (initialDiagram f)
      (initial (ParameterModels.supported f)) (initial_point (ParameterModels.supported f))
      (initial_naturality (ParameterModels.supported f)) X)
    (DiagramRowInterchange.cone_point squareFunctor (initialDiagram f)
      (initial (ParameterModels.supported f)) (initial_point (ParameterModels.supported f))
      (initial_naturality (ParameterModels.supported f)) X)
    (returnedBoundaryMovement f X)
    ((initialCell f X).postcomp (originalRowInclusion f X))
    (returnedBoundaryCell f X) (returnedBoundaryPasting f X) (originalBoundaryNull f X)

end Quillen.PerfectComplexes.ParameterTensorSupportedRow
