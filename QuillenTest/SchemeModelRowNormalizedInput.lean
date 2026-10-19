/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.KTheory.Bass.SchemeModelRowNormalizedInput

/-!
# Actual Model inputs preserve the whole normalized-boundary presentation

The original unit-preserving transformation determines the cell square through
its proved independent-cell comparison. Whole normalization naturality then
retains every normalization time, before descending to the canonical telescope.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Opposite AlgebraicGeometry Quillen.LoopPrespectrum
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace QuillenTest.SchemeModelRowNormalizedInput
open Quillen.KTheory.Bass SchemeModelRowSeed
open NaturalTrack GeometricSeedCospan ModelRowZigzagSequentialization
open GeometricSquareInterchange ModelDiagramRowInterchange
open scoped _root_.Topology unitInterval
variable (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
  (unit : ∀ X, 𝟭 (M.obj (laurent.op.obj X)) ≅ 𝟭 (M.obj (laurent.op.obj X)))
  (hunit : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M.map (laurent.op.map g)).functor (unit X) (unit Y))
  (M' : Scheme.{u}ᵒᵖ ⥤ Model.{w})
  (unit' : ∀ X, 𝟭 (M'.obj (laurent.op.obj X)) ≅ 𝟭 (M'.obj (laurent.op.obj X)))
  (hunit' : ∀ {X Y} (g : X ⟶ Y),
    Preserves (M'.map (laurent.op.map g)).functor (unit' X) (unit' Y))
  (η : M ⟶ M')
  (hη : ∀ X, Preserves (η.app (laurent.op.obj X)).functor (unit X) (unit' X))

example (i : ℕ) (X : Scheme.{u}ᵒᵖ) (n : ℕ) (s : unitInterval)
    (x : (vertex squareFunctor M X i).space n) :
    (targetInput M M' η i X).map n
        ((normalizedBoundaryCurrentHomotopy M unit hunit i X).level n (s, x)) =
      (normalizedBoundaryCurrentHomotopy M' unit' hunit' i X).level n
        (s, (stageInput M M' η i X).map n x) :=
  normalizedInput_homotopy M unit hunit M' unit' hunit' η hη i X n s x

example (X : Scheme.{u}ᵒᵖ) :
    (SchemeNaturalSeed.currentInputMap
      (ofModelUnits laurent.op coefficient M unit hunit)
      (ofModelUnits laurent.op coefficient M' unit' hunit')
      (Functor.whiskerRight η prespectrumFunctor)
      (inputEquivariance M unit hunit M' unit' hunit' η hη)).app X ≫
        normalizedComparison M' unit' hunit' X =
      normalizedComparison M unit hunit X ≫
        normalizedInputMap M unit hunit M' unit' hunit' η hη X :=
  normalizedComparison_inputMap M unit hunit M' unit' hunit' η hη X

end QuillenTest.SchemeModelRowNormalizedInput
