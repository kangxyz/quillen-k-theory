/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputChartNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputNormalizationPrismNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalEvaluationUnit
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveCutOpenCompactFamily
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceReanchorAttachment

/-!
# The actual objectwise two-tip evaluation carrier

The polynomial evaluation edge attaches to the original positive chart's full cut nodes.
The second sheet retains the strict forward Laurent unit before that same ordinary anchor.
Both cone tips remain distinct, and all original geometric chart parameters are available.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedEvaluationCarrier
open GlobalSectionChangeIndex CommonReferenceNerve
variable (X : Scheme.{u})

/-- Original strict polynomial pullback followed by polynomial evaluation. -/
abbrev polyRef := globalModel.map (projection.app X).op ≫ evaluationModel (op (polynomial.obj X))

/-- The actual normalized positive raw chart. -/
abbrev chart := evaluationRawMap (plus.app X)

/-- The original strict Laurent pullback followed by Laurent evaluation. -/
abbrev laurentRef := InputChartSimplex.sourceMap X

/-- The two full polynomial evaluation nodes, with the original comparison anchor. -/
def polynomialNodes : Fin 2 → Node (polyRef X) := fun i =>
  ⟨InputNormalizationPrism.firstVertices (projection.app X) i,
    InputNormalizationPrism.firstAnchors (projection.app X) i⟩


/-- The source polynomial node retains the full identity reference. -/
theorem polynomialNodes_zero : polynomialNodes X 0 = ⟨polyRef X, Iso.refl _⟩ := rfl

/-- The target polynomial node retains the original evaluation reference itself. -/
theorem polynomialNodes_one : polynomialNodes X 1 =
    ⟨evaluationModel (op X) ≫ evaluationRawMap (projection.app X),
      evaluationComparisonIso (projection.app X)⟩ := rfl

/-- The ordinary anchor is the complete original positive cut reference. -/
def ordinary : (laurentRef X).functor ≅ (polyRef X ≫ chart X).functor :=
  (InputChartSimplex.chartNodes X (plus.app X) (GlobalRawBass.plus_projection X) 3).2

/-- The actual strict forward Laurent unit, postwhiskered by original evaluation. -/
def commonUnit : (laurentRef X).functor ≅ (laurentRef X).functor :=
  isoWhiskerRight
    (onFunctor (globalModel.map (GlobalRawBass.laurentProjection.app X).op).functor
      (GlobalSchemeLaurentTrack.unit (op X)))
    (evaluationModel (op (laurent.obj X))).functor


/-- Original evaluation transports the actual strict unit to its unchanged target action. -/
theorem commonUnit_eq_target : commonUnit X =
    onFunctor (laurentRef X).functor
      (evaluationSmallUnit (op (laurent.obj X))
        (GlobalSchemeLaurentTrack.laurentScalar (op X))) := by
  apply Iso.ext
  apply NatTrans.ext
  funext A
  exact evaluationModel_unit (op (laurent.obj X))
    (GlobalSchemeLaurentTrack.laurentScalar (op X))
    ((globalModel.map (GlobalRawBass.laurentProjection.app X).op).functor.obj A)

/-- The second attachment retains the original unit before the complete ordinary anchor. -/
def shifted : (laurentRef X).functor ≅ (polyRef X ≫ chart X).functor :=
  commonUnit X ≪≫ ordinary X

/-- The two actual polynomial cylinders share their Laurent nerve but keep separate tips. -/
abbrev Carrier := CutOpenCarrier.space (polyRef X) (chart X) (laurentRef X)
  (ordinary X) (shifted X)

/-- The complete original polynomial comparison edge, before positive chart attachment. -/
def movement : C(I, |nerve (Codiscrete (Node (polyRef X)))|) :=
  (parameter (polyRef X) (polynomialNodes X)).comp (edge (k := 1) 0 1).toContinuousMap

/-- Every polynomial movement value is the unchanged evaluation comparison. -/
theorem movement_native (n : ℕ) (t : I)
    (x : (prespectrum (globalModel.obj (op X))).space n) :
    pointwisePrespectrumFamily (polyRef X) n (movement X t) x =
      (evaluationComparison (projection.app X)).level n (t, x) := by
  change pointwisePrespectrumFamily (polyRef X) n
    (parameter _ _ (edge (k := 1) 0 1 t)) x = _
  rw [pointwisePrespectrumFamily_parameter, prespectrumFamily_eq]
  exact InputNormalizationPrism.first_native (projection.app X) n t x

/-- The ordered polynomial edge in the original common chart simplex. -/
def polynomialFace : ⦋1⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![3, 4], by decide⟩

/-- Both attached nodes keep their entire original Model arrows and reference isomorphisms. -/
theorem polynomial_nodes (i : Fin 2) :
    InputChartSimplex.nodes X (polynomialFace.toOrderHom i) =
      attachPostcompNode (polyRef X) (chart X) (laurentRef X) (ordinary X)
        (polynomialNodes X i) := by
  fin_cases i
  · apply Sigma.ext
    · rfl
    apply heq_of_eq
    change ordinary X = ordinary X ≪≫ isoWhiskerRight (Iso.refl _) (chart X).functor
    rw [isoWhiskerRight_refl]
    exact (Iso.trans_refl _).symm
  · apply Sigma.ext
    · rfl
    apply heq_of_eq
    have hh : InputSimplex.anchors (plus.app X) (projection.app X) 3 ≪≫
        evaluationCompositionSecondIso (plus.app X) (projection.app X) =
        InputSimplex.anchors (plus.app X) (projection.app X) 4 :=
      Iso.ext (evaluationComposition_pasting (plus.app X) (projection.app X)).symm
    change eqToIso _ ≪≫ InputSimplex.anchors (plus.app X) (projection.app X) 4 =
      (eqToIso _ ≪≫ InputSimplex.anchors (plus.app X) (projection.app X) 3) ≪≫
        evaluationCompositionSecondIso (plus.app X) (projection.app X)
    rw [Iso.trans_assoc, hh]

/-- The entire polynomial edge attaches before evaluation, including its original clock. -/
theorem movement_attach (t : I) :
    parameter (laurentRef X) (InputChartSimplex.nodes X) (edge (k := 7) 3 4 t) =
      mapParameter (attachPostcompNode (polyRef X) (chart X) (laurentRef X) (ordinary X))
        (movement X t) := by
  change parameter _ _ _ = mapParameter _ (parameter _ _ (edge (k := 1) 0 1 t))
  rw [mapParameter_parameter]
  have h := parameter_face (laurentRef X) (InputChartSimplex.nodes X)
    polynomialFace (edge (k := 1) 0 1 t)
  have he : StdSimplex.map polynomialFace.toOrderHom (edge (k := 1) 0 1 t) =
      edge (k := 7) 3 4 t :=
    StdSimplex.map_duple (unitInterval.nonneg (unitInterval.symm t))
      (unitInterval.nonneg t) (by simp) 0 1 polynomialFace.toOrderHom
  rw [he] at h
  exact h.trans (congrArg (fun N => parameter (laurentRef X) N (edge (k := 1) 0 1 t))
    (funext (polynomial_nodes X)))

/-- The same entire edge attaches to the separately unit-shifted cone sheet. -/
theorem shifted_movement_attach (t : I) :
    mapParameter (CommonReferenceProduct.reanchor (commonUnit X))
      (parameter (laurentRef X) (InputChartSimplex.nodes X) (edge (k := 7) 3 4 t)) =
      mapParameter (attachPostcompNode (polyRef X) (chart X) (laurentRef X) (shifted X))
        (movement X t) := by
  rw [movement_attach]
  exact reanchor_attach_parameter (polyRef X) (chart X) (laurentRef X)
    (commonUnit X) (ordinary X) (movement X t)

/-- The two genuine tips remain distinct before native evaluation. -/
theorem tips_distinct :
    CutOpenCarrier.tipMinus (polyRef X) (chart X) (laurentRef X) (ordinary X) (shifted X) ≠
      CutOpenCarrier.tipPlus (polyRef X) (chart X) (laurentRef X) (ordinary X) (shifted X) :=
  CutOpenCarrier.tips_ne _ _ _ _ _

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputSeedEvaluationCarrier
