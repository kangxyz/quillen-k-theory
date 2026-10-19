/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputDescNative
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCompactAttachment
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCompactPrecompAttachment

/-!
# Both whole selected descent surfaces in the mixed input reference

The original Y descent surface after raw Laurent pullback and the original X descent surface
after strict input pullback have compact parameters in one actual common-reference nerve.
Their complete two-dimensional families, including the selected constant-path insertions,
are preserved. This does not identify the additional mixed cone boundary faces or fill them.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputMixedDesc
open GlobalSectionChangeIndex

/-- The exact compact nerve parameter of the already selected original descent surface. -/
def descParameter (X : Scheme.{u}) :=
  (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X) (InputChartSimplex.nodes X)).comp
    InputChartSimplex.descParameter.toContinuousMap

/-- Every point retains the entire original descent family and all selected half clocks. -/
theorem desc_parameter_native (X : Scheme.{u}) (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op X))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputChartSimplex.sourceMap X)
      (descParameter X) n ((r, s), x) = (descPasting X).level n (r, (s, x)) := by
  have h := congrArg (fun F => F (InputChartSimplex.descParameter (r, s), x))
    (CommonReferenceNerve.prespectrumFamily_eq (InputChartSimplex.sourceMap X)
      (InputChartSimplex.nodes X) n)
  exact (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ (descParameter X)
    (InputChartSimplex.nodes X) (r, s) (InputChartSimplex.descParameter (r, s)) rfl n x).trans
      (h.trans (InputChartSimplex.desc_native X n r s x))

/-- The same scalar surface descends through the original three-side parameter quotient. -/
def descSquareParameter (X : Scheme.{u}) :=
  (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X) (InputChartSimplex.nodes X)).comp
    (Quillen.SimplexParameters.collapsed InputChartSimplex.descParameter)

/-- The entire original moving square, including its quotient-collapse clock, is recovered. -/
theorem desc_square_parameter_native (X : Scheme.{u}) (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op X))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputChartSimplex.sourceMap X)
      (descSquareParameter X) n ((r, s), x) = (descPasting X).toSquare.level n (r, (s, x)) := by
  have h := congrArg
    (fun F => F (Quillen.SimplexParameters.collapsed InputChartSimplex.descParameter (r, s), x))
    (CommonReferenceNerve.prespectrumFamily_eq (InputChartSimplex.sourceMap X)
      (InputChartSimplex.nodes X) n)
  exact (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ (descSquareParameter X)
    (InputChartSimplex.nodes X) (r, s)
    (Quillen.SimplexParameters.collapsed InputChartSimplex.descParameter (r, s)) rfl n x).trans
      (h.trans (Quillen.SimplexParameters.HomotopyLift.toSquare (InputChartSimplex.simplex X)
        (InputChartSimplex.desc_native X) n r s x))

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The mixed reference is the original strict total Laurent pullback followed by evaluation. -/
def sourceMap :=
  globalModel.map ((laurent.map g) ≫ GlobalRawBass.laurentProjection.app Y).op ≫
    evaluationModel (op (laurent.obj X))

/-- The postcomposed Y surface keeps the original first evaluation comparison as reference. -/
def postSourceIso : (sourceMap g).functor ≅
    (InputChartSimplex.sourceMap Y ≫ evaluationRawMap (laurent.map g)).functor :=
  evaluationCompositionFirstIso (laurent.map g) (GlobalRawBass.laurentProjection.app Y)

/-- Every original Y node is postcomposed and anchored with its full specified comparison. -/
def postNode := CommonReferenceNerve.attachPostcompNode (InputChartSimplex.sourceMap Y)
  (evaluationRawMap (laurent.map g)) (sourceMap g) (postSourceIso g)

/-- The whole selected Y descent surface in the mixed common reference. -/
def postParameter :=
  (CommonReferenceNerve.mapParameter (postNode g)).comp (descParameter Y)

/-- The X reference retains the actual Laurent square and strict composition transport. -/
def preSourceIso : (sourceMap g).functor ≅
    (globalModel.map g.op ≫ InputChartSimplex.sourceMap X).functor :=
  eqToIso (congrArg (fun k : laurent.obj X ⟶ Y =>
    (globalModel.map k.op ≫ evaluationModel (op (laurent.obj X))).functor)
      (GlobalRawBass.laurentProjection.naturality g)) ≪≫
  eqToIso (congrArg (fun S => S ⋙ (evaluationModel (op (laurent.obj X))).functor)
    (globalReindex_comp (GlobalRawBass.laurentProjection.app X) g)) ≪≫
  Functor.associator (globalModel.map g.op).functor
    (globalModel.map (GlobalRawBass.laurentProjection.app X).op).functor
      (evaluationModel (op (laurent.obj X))).functor

/-- Every original X node is strictly precomposed with its full original reference. -/
def preNode := CommonReferenceNerve.attachPrecompNode (InputChartSimplex.sourceMap X)
  (globalModel.map g.op) (sourceMap g) (preSourceIso g)

/-- The whole selected X descent surface in the same mixed common reference. -/
def preParameter :=
  (CommonReferenceNerve.mapParameter (preNode g)).comp (descParameter X)

/-- The Y face is the original whole descent surface after the actual raw Laurent map. -/
theorem post_parameter_native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (sourceMap g) (postParameter g)
      n ((r, s), x) =
    (prespectrumMap (evaluationRawMap (laurent.map g))).map n
      ((descPasting Y).level n (r, (s, x))) := by
  change CommonReferenceNerve.compactPrespectrumFamily (sourceMap g)
    ((CommonReferenceNerve.mapParameter (CommonReferenceNerve.attachPostcompNode
      (InputChartSimplex.sourceMap Y) (evaluationRawMap (laurent.map g))
      (sourceMap g) (postSourceIso g))).comp (descParameter Y)) n ((r, s), x) = _
  rw [CommonReferenceNerve.compactPrespectrumFamily_attachPostcomp]
  exact congrArg ((prespectrumMap (evaluationRawMap (laurent.map g))).map n)
    (desc_parameter_native Y n r s x)

/-- The X face is the original whole descent surface after the actual strict input map. -/
theorem pre_parameter_native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (sourceMap g) (preParameter g)
      n ((r, s), x) =
    (descPasting X).level n (r, (s, (prespectrumMap (globalModel.map g.op)).map n x)) := by
  change CommonReferenceNerve.compactPrespectrumFamily (sourceMap g)
    ((CommonReferenceNerve.mapParameter (CommonReferenceNerve.attachPrecompNode
      (InputChartSimplex.sourceMap X) (globalModel.map g.op)
      (sourceMap g) (preSourceIso g))).comp (descParameter X)) n ((r, s), x) = _
  rw [CommonReferenceNerve.compactPrespectrumFamily_attachPrecomp]
  exact desc_parameter_native X n r s _

/-- The whole selected Y moving square retains the actual quotient before postcomposition. -/
def postSquareParameter :=
  (CommonReferenceNerve.mapParameter (postNode g)).comp (descSquareParameter Y)

/-- The whole selected X moving square keeps the actual three-side quotient after precomposition. -/
def preSquareParameter :=
  (CommonReferenceNerve.mapParameter (preNode g)).comp (descSquareParameter X)

/-- Every point of the prescribed Y `toSquare` face survives the actual raw Laurent postmap. -/
theorem post_square_parameter_native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (sourceMap g) (postSquareParameter g)
      n ((r, s), x) =
    (prespectrumMap (evaluationRawMap (laurent.map g))).map n
      ((descPasting Y).toSquare.level n (r, (s, x))) := by
  change CommonReferenceNerve.compactPrespectrumFamily (sourceMap g)
    ((CommonReferenceNerve.mapParameter (CommonReferenceNerve.attachPostcompNode
      (InputChartSimplex.sourceMap Y) (evaluationRawMap (laurent.map g))
      (sourceMap g) (postSourceIso g))).comp (descSquareParameter Y)) n ((r, s), x) = _
  rw [CommonReferenceNerve.compactPrespectrumFamily_attachPostcomp]
  exact congrArg ((prespectrumMap (evaluationRawMap (laurent.map g))).map n)
    (desc_square_parameter_native Y n r s x)

/-- Every point of the prescribed X `toSquare` face survives the actual strict input premap. -/
theorem pre_square_parameter_native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (sourceMap g) (preSquareParameter g)
      n ((r, s), x) =
    (descPasting X).toSquare.level n
      (r, (s, (prespectrumMap (globalModel.map g.op)).map n x)) := by
  change CommonReferenceNerve.compactPrespectrumFamily (sourceMap g)
    ((CommonReferenceNerve.mapParameter (CommonReferenceNerve.attachPrecompNode
      (InputChartSimplex.sourceMap X) (globalModel.map g.op)
      (sourceMap g) (preSourceIso g))).comp (descSquareParameter X)) n ((r, s), x) = _
  rw [CommonReferenceNerve.compactPrespectrumFamily_attachPrecomp]
  exact desc_square_parameter_native X n r s _

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputMixedDesc
