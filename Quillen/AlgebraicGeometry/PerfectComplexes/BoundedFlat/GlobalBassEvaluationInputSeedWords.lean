/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationSeed
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputSeed
public import Quillen.Topology.Prespectrum.NativeHomotopyCells

/-!
# The two prescribed original input and seed words

The strict seed is naturally identified using its actual whole-word natural transformation.
Both routes below have the same literal endpoints. The three-piece route retains its selected
outer half and inner half clocks. These are the specified words for the next relative square;
no relative filler or seed coherence is asserted in this file.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Topology unitInterval
universe u w v
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedWords
open GlobalSectionChangeIndex Quillen.NativePathCells

private theorem geometric_seed_naturality
    (F : Scheme.{u}ᵒᵖ ⥤ LoopPrespectrum.{w})
    (A : ∀ Z, Homotopy
      (((Quillen.KTheory.Bass.GeometricSquareInterchange.geometricSquare F).left.hom ≫
        (Quillen.KTheory.Bass.GeometricSquareInterchange.geometricSquare F).hom.right).app Z)
      (((Quillen.KTheory.Bass.GeometricSquareInterchange.geometricSquare F).left.hom ≫
        (Quillen.KTheory.Bass.GeometricSquareInterchange.geometricSquare F).hom.right).app Z))
    (hA : Quillen.KTheory.Bass.HomotopyWord.Natural A)
    {Z W : Scheme.{u}ᵒᵖ} (f : Z ⟶ W) :
    F.map f ≫ (Quillen.KTheory.Bass.WholeSeedCospan.seed
      (Quillen.KTheory.Bass.GeometricSquareInterchange.geometricSquare F) A hA).app W =
    (Quillen.KTheory.Bass.WholeSeedCospan.seed
      (Quillen.KTheory.Bass.GeometricSquareInterchange.geometricSquare F) A hA).app Z ≫
      ((Quillen.KTheory.Bass.strictDiagramFunctor squareFunctor).obj F).map f :=
  (Quillen.KTheory.Bass.WholeSeedCospan.seed
    (Quillen.KTheory.Bass.GeometricSquareInterchange.geometricSquare F) A hA).naturality f

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The original strict one-step input map used by the fixed whole evaluation homotopy. -/
def strictInput :=
  (((Quillen.KTheory.Bass.strictDiagramFunctor squareFunctor).obj
    GlobalSchemeLaurentTrack.diagram).map g.op)

/-- The original strict Laurent seed is natural as its actual whole-word transformation. -/
theorem strict_seed_naturality :
    sectionMap g ≫ strictSeed X = strictSeed Y ≫ strictInput g := by
  apply Hom.ext
  funext n
  have h := congrArg (fun k => k.map n)
    (@geometric_seed_naturality.{u, u + 1}
      GlobalSchemeLaurentTrack.diagram
      (Quillen.KTheory.Bass.GeometricSeedCospan.sourceTrack
        GlobalSchemeLaurentTrack.diagram GlobalSchemeLaurentTrack.homotopy)
      (Quillen.KTheory.Bass.GeometricSeedCospan.sourceTrack_naturality
        GlobalSchemeLaurentTrack.diagram GlobalSchemeLaurentTrack.homotopy
        GlobalSchemeLaurentTrack.homotopy_naturality)
      (op Y) (op X) g.op)
  have hx := congrArg (fun k => k.map n) (strictSeed_eq_wholeSeed X)
  have hy := congrArg (fun k => k.map n) (strictSeed_eq_wholeSeed Y)
  change ((strictSeed X).map n).comp ((sectionMap g).map n) =
    ((strictInput g).map n).comp ((strictSeed Y).map n)
  rw [hx, hy]
  exact h

/-- First traverse the fixed whole input homotopy at the original strict seed. -/
def inputFirst := Homotopy.precomp (strictSeed Y) (InputNaturality.stepHomotopy g)

/-- The original Y seed comparison is followed by the independently defined raw input map. -/
def seedSecond : Homotopy
    (strictSeed Y ≫ (stepEvaluation Y ≫ GlobalRawBass.map g))
    (evaluation Y ≫ (GlobalRawBass.transition Y ≫ GlobalRawBass.map g)) :=
  ((seedHomotopy Y).postcomp (GlobalRawBass.map g)).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- Base evaluation precedes the already selected original raw transition comparison. -/
def transitionThird :=
  Homotopy.precomp (evaluation Y) (GlobalRawBass.transitionInputHomotopy g)

/-- The original X seed comparison, with only its source strict naturality transported. -/
def seedFirst : Homotopy
    (strictSeed Y ≫ (strictInput g ≫ stepEvaluation X))
    (sectionMap g ≫ (evaluation X ≫ GlobalRawBass.transition X)) :=
  (Homotopy.precomp (sectionMap g) (seedHomotopy X)).cast
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun f => f ≫ stepEvaluation X) (strict_seed_naturality g)).trans
        (Category.assoc _ _ _))) rfl

/-- The original base-input evaluation comparison is followed by the unchanged raw seed. -/
def evaluationSecond : Homotopy
    (sectionMap g ≫ (evaluation X ≫ GlobalRawBass.transition X))
    (evaluation Y ≫ (boundedFlatPerfectPrespectrumMap g ≫ GlobalRawBass.transition X)) :=
  ((evaluationComparison g).postcomp (GlobalRawBass.transition X)).cast
    (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- The specified three-piece route keeps its original half and quarter subdivisions. -/
def longRoute : Homotopy
    (strictSeed Y ≫ (strictInput g ≫ stepEvaluation X))
    (evaluation Y ≫ (boundedFlatPerfectPrespectrumMap g ≫ GlobalRawBass.transition X)) :=
  (inputFirst g).trans ((seedSecond g).trans (transitionThird g))

/-- The specified two-piece route keeps both original selected comparisons. -/
def shortRoute : Homotopy
    (strictSeed Y ≫ (strictInput g ≫ stepEvaluation X))
    (evaluation Y ≫ (boundedFlatPerfectPrespectrumMap g ≫ GlobalRawBass.transition X)) :=
  (seedFirst g).trans (evaluationSecond g)

/-- The first half retains the fixed whole cone homotopy and independent output-loop time. -/
theorem inputFirst_apply (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((inputFirst g).level n (r, x)) s =
      (InputNaturality.coneHomotopy g).level n
        (r, Path.toContinuousMap ((strictSeed Y).map n x) s) := rfl

/-- The second piece retains the original Y conjugation under the actual raw cone input. -/
theorem seedSecond_apply (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((seedSecond g).level n (r, x)) s =
      (GlobalRawBass.coneMap g).map n ((conjugation Y).level n (r, (s, x))) := rfl

/-- The third piece retains the original raw conjugation at the evaluated source input. -/
theorem transitionThird_apply (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((transitionThird g).level n (r, x)) s =
      (GlobalRawBass.InputSeed.conjugateComparison g).level n
        (r, (s, (evaluation Y).map n x)) := rfl

/-- The short route begins with the unchanged X conjugation at the actual strict input. -/
theorem seedFirst_apply (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((seedFirst g).level n (r, x)) s =
      (conjugation X).level n (r, (s, (sectionMap g).map n x)) := rfl

/-- The short route ends at the original raw seed on the actual moving evaluation input. -/
theorem evaluationSecond_apply (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((evaluationSecond g).level n (r, x)) s =
      Path.toContinuousMap ((GlobalRawBass.transition X).map n
        ((evaluationComparison g).level n (r, x))) s := rfl

/-- The long route's entire first half is the original cone input homotopy on the seed. -/
theorem long_first (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((longRoute g).level n (lower r, x)) s =
      (InputNaturality.coneHomotopy g).level n
        (r, Path.toContinuousMap ((strictSeed Y).map n x) s) :=
  (congrArg (fun γ => Path.toContinuousMap γ s)
    (Homotopy.trans_lower_cell (inputFirst g)
      ((seedSecond g).trans (transitionThird g)) n r x)).trans
        (inputFirst_apply g n r s x)

/-- The entire middle quarter is the original Y seed comparison after raw cone input. -/
theorem long_second (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((longRoute g).level n (upper (lower r), x)) s =
      (GlobalRawBass.coneMap g).map n ((conjugation Y).level n (r, (s, x))) :=
  (congrArg (fun γ => Path.toContinuousMap γ s)
    ((Homotopy.trans_upper_cell (inputFirst g)
      ((seedSecond g).trans (transitionThird g)) n (lower r) x).trans
        (Homotopy.trans_lower_cell (seedSecond g) (transitionThird g) n r x))).trans
          (seedSecond_apply g n r s x)

/-- The final quarter is the already chosen original raw transition comparison. -/
theorem long_third (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((longRoute g).level n (upper (upper r), x)) s =
      (GlobalRawBass.InputSeed.conjugateComparison g).level n
        (r, (s, (evaluation Y).map n x)) :=
  (congrArg (fun γ => Path.toContinuousMap γ s)
    ((Homotopy.trans_upper_cell (inputFirst g)
      ((seedSecond g).trans (transitionThird g)) n (upper r) x).trans
        (Homotopy.trans_upper_cell (seedSecond g) (transitionThird g) n r x))).trans
          (transitionThird_apply g n r s x)

/-- The short route's first half is the original X seed comparison at the strict input. -/
theorem short_first (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((shortRoute g).level n (lower r, x)) s =
      (conjugation X).level n (r, (s, (sectionMap g).map n x)) :=
  (congrArg (fun γ => Path.toContinuousMap γ s)
    (Homotopy.trans_lower_cell (seedFirst g) (evaluationSecond g) n r x)).trans
      (seedFirst_apply g n r s x)

/-- The second short half retains the unchanged seed on the actual evaluation input. -/
theorem short_second (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((shortRoute g).level n (upper r, x)) s =
      Path.toContinuousMap ((GlobalRawBass.transition X).map n
        ((evaluationComparison g).level n (r, x))) s :=
  (congrArg (fun γ => Path.toContinuousMap γ s)
    (Homotopy.trans_upper_cell (seedFirst g) (evaluationSecond g) n r x)).trans
      (evaluationSecond_apply g n r s x)

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedWords
