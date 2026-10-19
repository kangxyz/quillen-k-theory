/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputCommutingSimplex
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputNormalizationPrism
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionChartRows

/-!
# The five original raw nodes inside the evaluation commuting diagram

The two actual binary normalization rows are identified as complete dependent nodes.
Their common total node fixes the full source transport of the second row.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputCommutingRawNodes
open GlobalSectionChangeIndex BassH0Merge BassH1Join

private theorem reanchor_pre {V W T : Model.{u}} {F K : V ⟶ T} (P : V ⟶ W)
    {H : W ⟶ T} (e : F.functor ≅ K.functor) (a : K.functor ≅ (P ≫ H).functor)
    (N : CommonReferenceNerve.Node H) :
    anchorNode e (preReferenceNode K P a N) = preReferenceNode F P (e ≪≫ a) N := by
  exact congrArg (fun b => (⟨P ≫ N.1, b⟩ : CommonReferenceNerve.Node F))
    (Iso.trans_assoc e a _).symm

/-- The three original normalization indices in the five-node evaluation simplex. -/
def binaryIndex : Fin 3 → Fin 5 := ![1, 2, 4]

/-- Evaluation preserves the complete original binary normalization nodes. -/
theorem binary_nodes {A B C : Scheme.{u}} (f : A ⟶ B) (v : B ⟶ C) (i : Fin 3) :
    InputCommutingSimplex.firstNodes f v (binaryIndex i) =
      preReferenceNode (InputSimplex.sourceMap f v) (evaluationModel (op C))
        (evaluationComparisonIso (f ≫ v)) (binaryNodes f v i) := by
  fin_cases i
  · exact (preReferenceNode_source _ _ (evaluationComparisonIso (f ≫ v))).symm
  · rfl
  · apply Sigma.ext
    · rfl
    apply heq_of_eq
    change evaluationComparisonIso (f ≫ v) ≪≫ evaluationCompositionTargetIso f v =
      evaluationComparisonIso (f ≫ v) ≪≫
        isoWhiskerLeft (evaluationModel (op C)).functor (BinaryNormalizationSimplex.total f v)
    rw [InputNormalizationPrism.normalization_target]

variable {A B C D : Scheme.{u}} (p : A ⟶ B) (v : B ⟶ C) (q : A ⟶ D) (w : D ⟶ C)
  (h : p ≫ v = q ≫ w)

private theorem second_binary_nodes (i : Fin 3) :
    InputCommutingSimplex.secondNodes p v q w h (binaryIndex i) =
      preReferenceNode (InputSimplex.sourceMap p v) (evaluationModel (op C))
        (InputCommutingSimplex.sourceIso p v q w h ≪≫ evaluationComparisonIso (q ≫ w))
        (binaryNodes q w i) := by
  change anchorNode (InputCommutingSimplex.sourceIso p v q w h)
    (InputCommutingSimplex.firstNodes q w (binaryIndex i)) = _
  rw [binary_nodes]
  exact reanchor_pre _ _ _ _

/-- The five raw indices retain both original normalization intermediates. -/
def rawIndex : Fin 5 → Fin 8 := ![1, 2, 4, 5, 7]

/-- Every full raw-square node occurs in the eight-node evaluation diagram. -/
theorem raw_nodes (i : Fin 5) :
    InputCommutingSimplex.nodes p v q w h (rawIndex i) =
      preReferenceNode (InputSimplex.sourceMap p v) (evaluationModel (op C))
        (evaluationComparisonIso (p ≫ v)) (NativeSquareFiveSimplex.nodes p v q w h i) := by
  have hs (j : Fin 3) :
      InputCommutingSimplex.secondNodes p v q w h (binaryIndex j) =
        preReferenceNode (InputSimplex.sourceMap p v) (evaluationModel (op C))
          (evaluationComparisonIso (p ≫ v))
          (NativeSquareFiveSimplex.nodes p v q w h
            (NativeSquareFiveSimplex.secondFace.toOrderHom j)) :=
    pre_families_match (InputSimplex.sourceMap p v) (evaluationModel (op C))
      (BinaryNormalizationSimplex.sourceMap q w) (binaryNodes q w)
      (second_binary_nodes p v q w h)
      (pre_square_second_nodes p v q w h (InputSimplex.sourceMap p v)
        (evaluationModel (op C)) (evaluationComparisonIso (p ≫ v))) 0
      ((InputCommutingSimplex.secondNodes_one p v q w h).trans
        ((binary_nodes p v 0).trans
          (pre_square_first_nodes p v q w h (InputSimplex.sourceMap p v)
            (evaluationModel (op C)) (evaluationComparisonIso (p ≫ v)) 0).symm)) j
  fin_cases i
  · exact binary_nodes p v 0
  · exact binary_nodes p v 1
  · exact binary_nodes p v 2
  · exact hs 1
  · exact hs 2

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputCommutingRawNodes
