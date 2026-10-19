/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.KTheory.Bass.SchemeModelRowNormalizedBoundary

/-!
# The canonical presentation with normalized independent boundary legs

The actual current telescope is a common stable refinement of this presentation
and the null-conjugated presentation. Every forward map is the independently
normalized Laurent cell followed by the original cone inclusion; its whole
normalization homotopy supplies the current-transition factorization.
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


/-- The proper-row presentation uses normalized boundary legs and original backward legs. -/
def normalizedPresentation (X : Scheme.{u}ᵒᵖ) : LoopPrespectrum.{w} :=
  Telescope.prespectrum
    (ZigzagSequentialization.stage
      (ModelRowZigzagSequentialization.vertex squareFunctor M X)
      (ModelRowZigzagSequentialization.target squareFunctor M X)
      (fun i => normalizedBoundary M unit hunit i X)
      (ModelRowZigzagSequentialization.backward squareFunctor M X))
    (ZigzagSequentialization.transition
      (ModelRowZigzagSequentialization.vertex squareFunctor M X)
      (ModelRowZigzagSequentialization.target squareFunctor M X)
      (fun i => normalizedBoundary M unit hunit i X)
      (ModelRowZigzagSequentialization.backward squareFunctor M X))

/-- The genuine original current telescope maps to the normalized-boundary row presentation. -/
def normalizedComparison (X : Scheme.{u}ᵒᵖ) :
    (SchemeNaturalSeed.currentTelescope
      (ofModelUnits laurent.op coefficient M unit hunit)).obj X ⟶
        normalizedPresentation M unit hunit X :=
  ZigzagSequentialization.telescopeMap
      (ModelRowZigzagSequentialization.vertex squareFunctor M X)
      (ModelRowZigzagSequentialization.target squareFunctor M X)
      (fun i => normalizedBoundary M unit hunit i X)
      (ModelRowZigzagSequentialization.backward squareFunctor M X)
      (fun i => (SchemeNaturalSeed.currentTransition
        (ofModelUnits laurent.op coefficient M unit hunit) i).app X)
      (fun i => normalizedBoundaryCurrentHomotopy M unit hunit i X)

/-- Every original finite-stage inclusion is preserved by the actual comparison. -/
@[reassoc] theorem normalizedComparison_inclusion (X : Scheme.{u}ᵒᵖ) (i : ℕ) :
    Telescope.inclusion (ModelRowZigzagSequentialization.vertex squareFunctor M X)
        (fun j => (SchemeNaturalSeed.currentTransition
          (ofModelUnits laurent.op coefficient M unit hunit) j).app X) i ≫
        normalizedComparison M unit hunit X =
      ZigzagSequentialization.comparison
          (ModelRowZigzagSequentialization.vertex squareFunctor M X)
          (ModelRowZigzagSequentialization.target squareFunctor M X)
          (fun j => normalizedBoundary M unit hunit j X)
          (ModelRowZigzagSequentialization.backward squareFunctor M X) i ≫
        Telescope.inclusion
          (ZigzagSequentialization.stage
            (ModelRowZigzagSequentialization.vertex squareFunctor M X)
            (ModelRowZigzagSequentialization.target squareFunctor M X)
            (fun j => normalizedBoundary M unit hunit j X)
            (ModelRowZigzagSequentialization.backward squareFunctor M X))
          (ZigzagSequentialization.transition
            (ModelRowZigzagSequentialization.vertex squareFunctor M X)
            (ModelRowZigzagSequentialization.target squareFunctor M X)
            (fun j => normalizedBoundary M unit hunit j X)
            (ModelRowZigzagSequentialization.backward squareFunctor M X)) i :=
  ZigzagSequentialization.inclusion_telescopeMap _ _ _ _ _ _ i

/-- Actual finite growth proves the normalized-boundary presentation comparison stable. -/
theorem normalizedComparison_stable (X : Scheme.{u}ᵒᵖ) :
    IsStableEquivalence (normalizedComparison M unit hunit X) :=
  ModelRowZigzagSequentialization.telescopeMap_stable squareFunctor M X
    (fun i => normalizedBoundary M unit hunit i X)
    (fun i => (SchemeNaturalSeed.currentTransition
      (ofModelUnits laurent.op coefficient M unit hunit) i).app X)
    (fun i => normalizedBoundaryCurrentHomotopy M unit hunit i X)

end Quillen.KTheory.Bass.SchemeModelRowSeed
