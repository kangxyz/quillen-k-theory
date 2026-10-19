/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.KTheory.Bass.SchemeModelRowNormalizedBoundary
import Quillen.Topology.Prespectrum.RowNormalizationPasting

/-! # Original normalized boundary at a symbolic Bass stage

The first face is the independent inverse-prefix operation followed by the original
inclusion. The last face is the actual current transition and proper-row backward map.
-/
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u w
namespace QuillenTest.SchemeModelRowNormalizedBoundary
open Quillen.KTheory.Bass GeometricSeedCospan NaturalTrack
variable (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)) ≅ 𝟭 (M.obj (laurent.op.obj X)))
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).functor (unit X) (unit Y))



/-- Every symbolic stage begins at the separately constructed normalized boundary operation. -/
theorem original_normalized_face (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (x : (((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor)).obj X).space n) :
    (SchemeModelRowSeed.normalizedBoundaryCurrentHomotopy M unit hunit i X).level n (0, x) =
      (SchemeModelRowSeed.normalizedBoundary M unit hunit i X).map n x :=
  (SchemeModelRowSeed.normalizedBoundaryCurrentHomotopy M unit hunit i X).at_zero n x

/-- Its final face retains the literal current transition and actual proper-row backward map. -/
theorem original_current_face (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ)
    (x : (((strictDiagramIterate squareFunctor i).obj (M ⋙ prespectrumFunctor)).obj X).space n) :
    (SchemeModelRowSeed.normalizedBoundaryCurrentHomotopy M unit hunit i X).level n (1, x) =
      (ModelRowZigzagSequentialization.backward squareFunctor M X i).map n
        (((SchemeNaturalSeed.currentTransition
          (ofModelUnits laurent.op coefficient M unit hunit) i).app X).map n x) :=
  (SchemeModelRowSeed.normalizedBoundaryCurrentHomotopy M unit hunit i X).at_one n x

end QuillenTest.SchemeModelRowNormalizedBoundary
