/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedTransitionFace
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedUnitNodes
import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedEvaluationUnitNerve

/-! Regression checks for the actual two-tip seed carrier and original unit/transition surfaces. -/
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace QuillenTest.GlobalBassEvaluationInputSeedCarrier
open GlobalBassEvaluation GlobalSectionChangeIndex CommonReferenceNerve
variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The two scalar endpoints remain genuinely distinct. -/
theorem distinct_tips :
    CutOpenCarrier.tipMinus (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
      (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g) ≠
    CutOpenCarrier.tipPlus (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
      (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g) :=
  InputSeedCarrier.tips_distinct g

/-- Strict seed naturality identifies the literal starting arrows of both prescribed words. -/
theorem strict_seed_endpoints :
    sectionMap g ≫ strictSeed X = strictSeed Y ≫ InputSeedWords.strictInput g :=
  InputSeedWords.strict_seed_naturality g

/-- The actual raw scalar includes the exact original pullback and zero normalization. -/
theorem actual_raw_unit :
    (InputSeedRawUnit.rawUnit g).hom =
      evaluationRawUnit (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y)
        (GlobalSchemeLaurentTrack.laurentScalar (op X)) :=
  InputSeedRawUnit.rawUnit_hom g

/-- The original common unit intertwines the full total-evaluation isomorphism. -/
theorem full_unit_square :
    InputSeedCarrier.commonUnit g ≪≫
      evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y) =
    evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y) ≪≫
      isoWhiskerLeft (evaluationModel (op Y)).functor (InputSeedRawUnit.rawUnit g) :=
  InputSeedRawUnit.evaluation_unit g

/-- The whole lower face retains all eight complete reference nodes. -/
theorem lower_nodes (i : Fin 8) :
    InputSeedUnitNodes.nodes g (InputSeedUnitNodes.lowerFace.toOrderHom i) =
      InputSeedUnitNodes.lower g i := InputSeedUnitNodes.lower_nodes g i

/-- The upper face retains all eight separate original unit-shifted references. -/
theorem upper_nodes (i : Fin 8) :
    InputSeedUnitNodes.nodes g (InputSeedUnitNodes.upperFace.toOrderHom i) =
      InputSeedUnitNodes.upper g i := InputSeedUnitNodes.upper_nodes g i

/-- The whole lower diagram is the actual original Laurent commuting square. -/
theorem lower_diagram :
    (InputSeedUnitNodes.simplex g).face InputSeedUnitNodes.lowerFace =
      InputCommutingSimplex.simplex (laurent.map g) (GlobalRawBass.laurentProjection.app Y)
        (GlobalRawBass.laurentProjection.app X) g
        (GlobalRawBass.laurentProjection.naturality g) := InputSeedUnitNodes.lower_face g

/-- The independently anchored upper diagram is the same entire original square. -/
theorem upper_diagram :
    (InputSeedUnitNodes.simplex g).face InputSeedUnitNodes.upperFace =
      InputCommutingSimplex.simplex (laurent.map g) (GlobalRawBass.laurentProjection.app Y)
        (GlobalRawBass.laurentProjection.app X) g
        (GlobalRawBass.laurentProjection.naturality g) := InputSeedUnitNodes.upper_face g

/-- Ordinary chart attachment agrees for every full raw polynomial node. -/
theorem ordinary_attachment (N : Node (InputSeedRawAttachment.rawPolyRef g)) :
    InputSeedRawUnit.evaluateNode g (InputSeedRawAttachment.rawOrdinaryNode g N) =
      InputSeedRawAttachment.ordinaryNode g (InputSeedRawAttachment.polynomialNode g N) :=
  InputSeedRawAttachment.ordinary_node g N

/-- The shifted attachment agrees before realization for every full raw polynomial node. -/
theorem shifted_attachment (N : Node (InputSeedRawAttachment.rawPolyRef g)) :
    InputSeedRawUnit.evaluateNode g (InputSeedRawAttachment.rawShiftedNode g N) =
      InputSeedRawAttachment.shiftedNode g (InputSeedRawAttachment.polynomialNode g N) :=
  InputSeedRawAttachment.shifted_node g N

/-- The whole raw carrier keeps the original native source after actual base evaluation. -/
theorem raw_carrier_native (n : ℕ) (y : GlobalRawBass.InputIdentitySeedCarrier.Carrier g)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    CutOpenCarrier.nativeEval (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
      (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g)
      n (InputSeedRawMap.map g y) x =
    CutOpenCarrier.nativeEval (GlobalRawBass.InputIdentitySeedCarrier.polyRef g)
      (InputSeedCarrier.chart (X := X)) (GlobalRawBass.InputIdentitySeedCarrier.laurentRef g)
      (GlobalRawBass.InputIdentitySeedCarrier.ordinary g)
      (GlobalRawBass.InputIdentitySeedCarrier.shifted g) n y
      ((prespectrumMap (evaluationModel (op Y))).map n x) :=
  InputSeedRawMap.native g n y x

/-- The entire third original word survives at all original comparison and loop times. -/
theorem original_third_piece (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    (GlobalRawBass.InputIdentityPositive.inclusion X).map n
      (CutOpenCarrier.nativeEval (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
        (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g) (InputSeedCarrier.shifted g)
        n (InputSeedTransitionFace.parameter g (r, s)) x) =
      Path.toContinuousMap ((InputSeedWords.transitionThird g).level n (r, x)) s :=
  InputSeedTransitionFace.native g n r s x

/-- The first entire edge is the exact original source word. -/
theorem transition_source (s : unitInterval) :
    InputSeedTransitionFace.parameter g (0, s) =
      InputSeedTransitionFace.sourceParameter g s := InputSeedTransitionFace.source g s

/-- The other entire edge is the exact original target word with its old parentheses. -/
theorem transition_target (s : unitInterval) :
    InputSeedTransitionFace.parameter g (1, s) =
      InputSeedTransitionFace.targetParameter g s := InputSeedTransitionFace.target g s

/-- The full lower scalar edge retains the actual ordinary tip. -/
theorem transition_zero (r : unitInterval) :
    InputSeedTransitionFace.parameter g (r, 0) =
      CutOpenCarrier.tipMinus (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
        (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g)
        (InputSeedCarrier.shifted g) := InputSeedTransitionFace.zero g r

/-- The full upper scalar edge retains the separate shifted tip. -/
theorem transition_one (r : unitInterval) :
    InputSeedTransitionFace.parameter g (r, 1) =
      CutOpenCarrier.tipPlus (InputSeedCarrier.polyRef g) (InputSeedCarrier.chart (X := X))
        (InputSeedCarrier.laurentRef g) (InputSeedCarrier.ordinary g)
        (InputSeedCarrier.shifted g) := InputSeedTransitionFace.one g r

/-- The first long half keeps the whole original input map and independent output-loop time. -/
theorem first_half_clock (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((InputSeedWords.longRoute g).level n
      (Quillen.NativePathCells.lower r, x)) s =
    (InputNaturality.coneHomotopy g).level n
      (r, Path.toContinuousMap ((strictSeed Y).map n x) s) :=
  InputSeedWords.long_first g n r s x

/-- The middle long quarter is the original Y seed followed by raw input. -/
theorem middle_quarter_clock (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((InputSeedWords.longRoute g).level n
      (Quillen.NativePathCells.upper (Quillen.NativePathCells.lower r), x)) s =
      (GlobalRawBass.coneMap g).map n ((conjugation Y).level n (r, (s, x))) :=
  InputSeedWords.long_second g n r s x

/-- The final long quarter retains the original raw transition at evaluated source input. -/
theorem final_quarter_clock (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((InputSeedWords.longRoute g).level n
      (Quillen.NativePathCells.upper (Quillen.NativePathCells.upper r), x)) s =
      (GlobalRawBass.InputSeed.conjugateComparison g).level n
        (r, (s, (GlobalBassEvaluation.evaluation Y).map n x)) := InputSeedWords.long_third g n r s x

/-- The first short half is the original X seed at the actual strict source map. -/
theorem short_first_clock (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((InputSeedWords.shortRoute g).level n
      (Quillen.NativePathCells.lower r, x)) s =
      (conjugation X).level n (r, (s, (sectionMap g).map n x)) :=
  InputSeedWords.short_first g n r s x

/-- The final short half keeps the original raw seed on the moving evaluation input. -/
theorem short_second_clock (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    Path.toContinuousMap ((InputSeedWords.shortRoute g).level n
      (Quillen.NativePathCells.upper r, x)) s =
      Path.toContinuousMap ((GlobalRawBass.transition X).map n
        ((evaluationComparison g).level n (r, x))) s := InputSeedWords.short_second g n r s x

/-- Arbitrary units retain the actual complete four-node native comparison. -/
theorem original_unit_surface (r : (Γ(X, ⊤))ˣ) :
    Quillen.SimplexParameters.HomotopyLift (InputSeedEvaluationUnit.simplex g r)
      InputSeedEvaluationUnit.scalarParameter (evaluationUnitPasting g r) :=
  InputSeedEvaluationUnit.native g r

/-- The final anchor retains the exact original normalized raw transformation. -/
theorem original_last_anchor (r : (Γ(X, ⊤))ˣ) :
    (InputSeedEvaluationUnit.anchors g r 3).hom = (evaluationComparisonIso g).hom ≫
      whiskerLeft (evaluationModel (op Y)).functor (evaluationRawUnit g r) :=
  InputSeedEvaluationUnit.last_anchor_hom g r

/-- The actual four-node nerve parameter is the whole original surface on every native input. -/
theorem original_unit_nerve (r : (Γ(X, ⊤))ˣ) (n : ℕ) (s t : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    pointwisePrespectrumFamily (InputSeedEvaluationUnit.sourceMap g) n
      (InputSeedEvaluationUnit.parameter g r (s, t)) x =
      (evaluationUnitPasting g r).level n (s, (t, x)) :=
  InputSeedEvaluationUnit.parameter_native g r n s t x

end QuillenTest.GlobalBassEvaluationInputSeedCarrier
