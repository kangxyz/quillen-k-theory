/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSeedCarrier
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputIdentitySeedUnitNodes
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalRawBassInputDescNodes

/-!
# Original raw Laurent units in the mixed two-sheet reference

The actual pulled-back Laurent scalar identifies the original normalized source unit.
Its entire evaluation comparison intertwines the strict common unit. Consequently every
complete raw reference node commutes with the two sheet attachments before realization.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedRawUnit
open GlobalSectionChangeIndex CommonReferenceNerve

private theorem reanchor_pre_unit {V W T : Model.{u}} (F : V ⟶ T)
    (J : V ⟶ W) (R : W ⟶ T) (e : F.functor ≅ (J ≫ R).functor)
    (α : F.functor ≅ F.functor) (β : R.functor ≅ R.functor)
    (h : α ≪≫ e = e ≪≫ isoWhiskerLeft J.functor β) (N : Node R) :
    CommonReferenceProduct.reanchor α (attachPrecompNode R J F e N) =
      attachPrecompNode R J F e (CommonReferenceProduct.reanchor β N) := by
  apply congrArg (fun ρ => (⟨J ≫ N.1, ρ⟩ : Node F))
  change α ≪≫ (e ≪≫ isoWhiskerLeft J.functor N.2) =
    e ≪≫ isoWhiskerLeft J.functor (β ≪≫ N.2)
  rw [isoWhiskerLeft_trans, ← Iso.trans_assoc, ← Iso.trans_assoc, h]

private theorem whisker_onFunctor {V W T : Model.{u}} (J : V ⟶ W) (R : W ⟶ T)
    (β : 𝟭 T.category ≅ 𝟭 T.category) :
    isoWhiskerLeft J.functor (Quillen.FunctorIdentityAutomorphism.onFunctor R.functor β) =
      Quillen.FunctorIdentityAutomorphism.onFunctor (J ≫ R).functor β := rfl

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The actual old binary source unit, including its chosen-zero normalization. -/
def rawUnit := UnitTrackPostcompSimplex.sourceUnit (laurent.map g)
  (GlobalRawBass.laurentProjection.app Y) (GlobalSchemeLaurentTrack.laurentScalar (op Y))

/-- The actual Laurent scalar pullback identifies this unchanged raw transformation. -/
theorem rawUnit_hom : (rawUnit g).hom =
    evaluationRawUnit (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y)
      (GlobalSchemeLaurentTrack.laurentScalar (op X)) := by
  change evaluationRawUnit (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y)
    (Units.map (laurent.map g).appTop.hom.toMonoidHom
      (GlobalSchemeLaurentTrack.laurentScalar (op Y))) = _
  rw [GlobalRawBass.laurentUnit_map]

/-- The original normalized source unit is the actual target identity action. -/
theorem rawUnit_eq_target : rawUnit g =
    Quillen.FunctorIdentityAutomorphism.onFunctor
      (GlobalRawBass.InputIdentitySeedUnitNodes.source g).functor
      (evaluationSmallUnit (op (laurent.obj X))
        (GlobalSchemeLaurentTrack.laurentScalar (op X))) :=
  Iso.ext ((rawUnit_hom g).trans
    (evaluationRawUnit_eq (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y)
      (GlobalSchemeLaurentTrack.laurentScalar (op X))))

/-- The complete original total-evaluation isomorphism intertwines the two original units. -/
theorem evaluation_unit :
    InputSeedCarrier.commonUnit g ≪≫
        evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y) =
      evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y) ≪≫
        isoWhiskerLeft (evaluationModel (op Y)).functor (rawUnit g) := by
  let e : (InputSeedCarrier.laurentRef g).functor ≅
      (evaluationModel (op Y) ≫ GlobalRawBass.InputIdentitySeedUnitNodes.source g).functor :=
    evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y)
  change InputSeedCarrier.commonUnit g ≪≫ e =
    e ≪≫ isoWhiskerLeft (evaluationModel (op Y)).functor (rawUnit g)
  have hwhisker := whisker_onFunctor (evaluationModel (op Y))
    (GlobalRawBass.InputIdentitySeedUnitNodes.source g)
    (evaluationSmallUnit (op (laurent.obj X))
      (GlobalSchemeLaurentTrack.laurentScalar (op X)))
  have hunit := congrArg (isoWhiskerLeft (evaluationModel (op Y)).functor)
    (rawUnit_eq_target g).symm
  have htransport := hwhisker.symm.trans hunit
  exact (InputSeedCarrier.anchor_unit g
    ⟨evaluationModel (op Y) ≫ GlobalRawBass.InputIdentitySeedUnitNodes.source g,
      e⟩).trans (congrArg (fun a => e ≪≫ a) htransport)

/-- The actual raw evaluation node retains its entire original reference isomorphism. -/
def evaluateNode (N : Node (GlobalRawBass.InputIdentitySeedUnitNodes.source g)) :
    Node (InputSeedCarrier.laurentRef g) :=
  attachPrecompNode (GlobalRawBass.InputIdentitySeedUnitNodes.source g)
    (evaluationModel (op Y)) (InputSeedCarrier.laurentRef g)
    (evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y)) N

/-- Evaluation agrees with the already used original rectangle-node attachment. -/
theorem evaluateNode_eq (N : Node (GlobalRawBass.InputIdentitySeedUnitNodes.source g)) :
    evaluateNode g N = GlobalRawBass.InputDescNodes.evaluateNode g N := rfl

/-- Both sheets commute as full dependent nodes, not merely as equal native values. -/
theorem evaluate_shift (N : Node (GlobalRawBass.InputIdentitySeedUnitNodes.source g)) :
    CommonReferenceProduct.reanchor (InputSeedCarrier.commonUnit g) (evaluateNode g N) =
      evaluateNode g (CommonReferenceProduct.reanchor (rawUnit g) N) :=
  reanchor_pre_unit (InputSeedCarrier.laurentRef g) (evaluationModel (op Y))
    (GlobalRawBass.InputIdentitySeedUnitNodes.source g)
    (evaluationComparisonIso (laurent.map g ≫ GlobalRawBass.laurentProjection.app Y))
    (InputSeedCarrier.commonUnit g) (rawUnit g) (evaluation_unit g) N

/-- The entire raw nerve parameter commutes with the same two original sheet attachments. -/
theorem evaluate_shift_parameter {k : ℕ}
    (N : Fin (k + 1) → Node (GlobalRawBass.InputIdentitySeedUnitNodes.source g))
    (z : Convexity.StdSimplex ℝ (Fin (k + 1))) :
    mapParameter (CommonReferenceProduct.reanchor (InputSeedCarrier.commonUnit g))
      (parameter (InputSeedCarrier.laurentRef g) (fun i => evaluateNode g (N i)) z) =
    parameter (InputSeedCarrier.laurentRef g)
      (fun i => evaluateNode g (CommonReferenceProduct.reanchor (rawUnit g) (N i))) z := by
  rw [mapParameter_parameter]
  exact congrArg (fun ns => parameter (InputSeedCarrier.laurentRef g) ns z)
    (funext fun i => evaluate_shift g (N i))

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedRawUnit
