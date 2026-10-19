/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputSimplex
public import Quillen.Waldhausen.SConstruction.Iterated.ScalarRouteExtraction
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexFacePrecompEvaluation
public import Quillen.Topology.Prespectrum.RelativePrecompLevel

/-!
# Whole native global evaluation composition in its actual simplex

The scalar parameter follows the already selected normalization and two-triangle pasting word.
Every equality retains both comparison coordinates, the entire half-clock seam, and all
prespectrum levels. No replacement evaluation comparison is selected here.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputSimplex
open GlobalSectionChangeIndex

private theorem pasting_native {V W : Model.{u}} {k : ℕ} (S : ModelSimplex V W k)
    {a b : StdSimplex ℝ (Fin (k + 1))} {p q z : Path a b}
    (J : p.Homotopy q) (K : p.Homotopy z) {F G G' H : V ⟶ W}
    (η : F.functor ⟶ G.functor) (θ : G.functor ⟶ H.functor)
    (η' : F.functor ⟶ G'.functor) (θ' : G'.functor ⟶ H.functor)
    (hη : ∀ A, W.waldhausen.weq (η.app A)) (hθ : ∀ A, W.waldhausen.weq (θ.app A))
    (hη' : ∀ A, W.waldhausen.weq (η'.app A)) (hθ' : ∀ A, W.waldhausen.weq (θ'.app A))
    (he : η ≫ θ = η' ≫ θ')
    (lJ : HomotopyLift S J (prespectrumTransformationCompositionHomotopy η θ hη hθ))
    (lK : HomotopyLift S K (prespectrumTransformationCompositionHomotopy η' θ' hη' hθ')) :
    HomotopyLift S (J.symm.trans K)
      (prespectrumPastingHomotopy η θ η' θ' hη hθ hη' hθ' he) := by
  unfold prespectrumPastingHomotopy
  apply HomotopyLift.trans S (HomotopyLift.symm S lJ)
  apply HomotopyLift.nativeCast S lK _ rfl
  congr 1
  exact he.symm

private theorem triangle_precomp_native {V W T : Model.{u}} {k : ℕ}
    (R : ModelSimplex V W 2) (S : ModelSimplex T W k) (J : T ⟶ V)
    (α : ⦋2⦌ ⟶ ⦋k⦌) (hface : S.face α = R.precomp J)
    {f g : prespectrum V ⟶ prespectrum W} {H K : Homotopy f g}
    (N : H.RelHomotopy K)
    (hN : ∀ (n : ℕ) (r s : unitInterval) (x : (prespectrum V).space n),
      prespectrumSimplexFamily R n
        (Quillen.TheoremB.compositionTriangleHomotopy (r, s), x) =
          N.level n (r, (s, x))) :
    HomotopyLift S (triangle α) (Homotopy.RelHomotopy.precomp (prespectrumMap J) N) := by
  intro n r s x
  exact prespectrumSimplexFamily_face_precomp R S J α hface
    Quillen.TheoremB.compositionTriangleHomotopy.toContinuousMap N hN n r s x

private theorem face_triangle_family {V W T : Model.{u}} {k : ℕ}
    (R : ModelSimplex V W 2) (S : ModelSimplex T W k) (J : T ⟶ V)
    (α : ⦋2⦌ ⟶ ⦋k⦌) (hface : S.face α = R.precomp J)
    (n : ℕ) (r s : unitInterval) (x : (prespectrum T).space n) :
    prespectrumSimplexFamily S n (triangle α (r, s), x) =
      prespectrumSimplexFamily R n
        (Quillen.TheoremB.compositionTriangleHomotopy (r, s), (prespectrumMap J).map n x) :=
  (prespectrumSimplexFamily_face S α n
    (Quillen.TheoremB.compositionTriangleHomotopy (r, s)) x).trans
    ((congrArg (fun Q => prespectrumSimplexFamily Q n
      (Quillen.TheoremB.compositionTriangleHomotopy (r, s), x)) hface).trans
      (prespectrumSimplexFamily_precomp R J n
        (Quillen.TheoremB.compositionTriangleHomotopy (r, s)) x))

private def scalarFamily {V W : Model.{u}} {k : ℕ} (S : ModelSimplex V W k)
    (P : C(unitInterval × unitInterval, StdSimplex ℝ (Fin (k + 1)))) (n : ℕ) :
    C(unitInterval × (unitInterval × (prespectrum V).space n), (prespectrum W).space n) :=
  (prespectrumSimplexFamily S n).comp ⟨fun z => (P (z.1, z.2.1), z.2.2), by fun_prop⟩

private theorem whole_face_precomp {V W T : Model.{u}} {k : ℕ}
    (R : ModelSimplex V W 2) (S : ModelSimplex T W k) (J : T ⟶ V)
    (α : ⦋2⦌ ⟶ ⦋k⦌) (hface : S.face α = R.precomp J) (n : ℕ) :
    scalarFamily S (triangle α).toContinuousMap n =
      (scalarFamily R Quillen.TheoremB.compositionTriangleHomotopy.toContinuousMap n).comp
        (Homotopy.RelHomotopy.precompParameter (prespectrumMap J) n) := by
  apply ContinuousMap.ext
  rintro ⟨r, s, x⟩
  exact face_triangle_family R S J α hface n r s x

private theorem lift_of_whole {V W : Model.{u}} {k : ℕ}
    (S : ModelSimplex V W k) {a b : StdSimplex ℝ (Fin (k + 1))}
    {p q : Path a b} (P : p.Homotopy q)
    {f g : prespectrum V ⟶ prespectrum W} {H K : Homotopy f g}
    (M : H.RelHomotopy K)
    (e : ∀ n, scalarFamily S P.toContinuousMap n = (M.level n).toContinuousMap) :
    HomotopyLift S P M := by
  intro n r s x
  exact DFunLike.congr_fun (e n) (r, (s, x))

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- The two original Model triangles use the native two-half comparison clock. -/
def modelParameter :=
  (triangle (triangleFace 0 1 4 (by decide) (by decide))).symm.trans
    (triangle (triangleFace 0 3 4 (by decide) (by decide)))

/-- The binary normalization remains under the unchanged first evaluation edge. -/
def splitParameter :=
  (Path.Homotopy.refl (edge (k := 4) 0 1)).hcomp
    (triangle (triangleFace 1 2 4 (by decide) (by decide)))

/-- The original outer comparison first reverses normalization, then follows Model pasting. -/
def compositionParameter := splitParameter.symm.trans modelParameter

/-- Every point of the first original Model triangle is preserved. -/
theorem total_native :
    HomotopyLift (simplex f g) (triangle (triangleFace 0 1 4 (by decide) (by decide)))
      (prespectrumTransformationCompositionHomotopy
        (F := sourceMap f g) (G := totalMap f g) (H := targetMap f g)
        (evaluationComparisonIso (f ≫ g)).hom (evaluationCompositionTargetIso f g).hom
        (fun _ => (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)
        (fun _ => (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)) :=
  triangle_lift _ _ _ _ _ _ (total_face f g)

/-- Every point of the original strict-cut Model triangle is preserved. -/
theorem cut_native :
    HomotopyLift (simplex f g) (triangle (triangleFace 0 3 4 (by decide) (by decide)))
      (prespectrumTransformationCompositionHomotopy
        (F := sourceMap f g) (G := cutMap f g) (H := targetMap f g)
        (evaluationCompositionFirstIso f g).hom (evaluationCompositionSecondIso f g).hom
        (fun _ => (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)
        (fun _ => (boundedFlatPerfectWaldhausen X).smallModel.weq_iso _ inferInstance)) :=
  triangle_lift _ _ _ _ _ _ (cut_face f g)

private def binaryModelComparison :=
  prespectrumTransformationCompositionHomotopy
    (F := BinaryNormalizationSimplex.sourceMap f g)
    (G := BinaryNormalizationSimplex.intermediateMap f g)
    (H := BinaryNormalizationSimplex.targetMap f g)
    (BinaryNormalizationSimplex.first f g).hom (BinaryNormalizationSimplex.second f g).hom
    (fun _ => (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
    (fun _ => (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)

private theorem whole_precomp (n : ℕ) :
    ((Homotopy.RelHomotopy.precomp (prespectrumMap (evaluationModel (op Z)))
      (boundedFlatNormalizedCompTrackComparison f g)).level n).toContinuousMap =
      ((boundedFlatNormalizedCompTrackComparison f g).level n).toContinuousMap.comp
        (Homotopy.RelHomotopy.precompParameter
          (prespectrumMap (evaluationModel (op Z))) n) :=
  Homotopy.RelHomotopy.precomp_level_toContinuousMap
    (prespectrumMap (evaluationModel (op Z))) (boundedFlatNormalizedCompTrackComparison f g) n

private theorem binary_model_whole (n : ℕ) :
    scalarFamily (BinaryNormalizationSimplex.simplex f g)
      Quillen.TheoremB.compositionTriangleHomotopy.toContinuousMap n =
      ((binaryModelComparison f g).level n).toContinuousMap := by
  apply ContinuousMap.ext
  rintro ⟨r, s, x⟩
  exact BinaryNormalizationSimplex.whole_triangle f g n r s x

private theorem binary_whole (n : ℕ) :
    scalarFamily (BinaryNormalizationSimplex.simplex f g)
      Quillen.TheoremB.compositionTriangleHomotopy.toContinuousMap n =
      ((boundedFlatNormalizedCompTrackComparison f g).level n).toContinuousMap :=
  (binary_model_whole f g n).trans (BinaryNormalizationSimplex.native_level f g n).symm

private theorem normalization_whole (n : ℕ) :
    scalarFamily (simplex f g)
      (triangle (triangleFace 1 2 4 (by decide) (by decide))).toContinuousMap n =
      ((Homotopy.RelHomotopy.precomp (prespectrumMap (evaluationModel (op Z)))
        (boundedFlatNormalizedCompTrackComparison f g)).level n).toContinuousMap :=
  (whole_face_precomp (BinaryNormalizationSimplex.simplex f g) (simplex f g)
    (evaluationModel (op Z)) (triangleFace 1 2 4 (by decide) (by decide))
    (normalization_face f g) n).trans
      ((congrArg (fun A => A.comp (Homotopy.RelHomotopy.precompParameter
        (prespectrumMap (evaluationModel (op Z))) n)) (binary_whole f g n)).trans
        (whole_precomp f g n).symm)

/-- The whole original binary comparison retains its precise evaluation whisker. -/
theorem normalization_native :
    HomotopyLift (simplex f g) (triangle (triangleFace 1 2 4 (by decide) (by decide)))
      (Homotopy.RelHomotopy.precomp (prespectrumMap (evaluationModel (op Z)))
        (boundedFlatNormalizedCompTrackComparison f g)) :=
  lift_of_whole (simplex f g) _ _ (normalization_whole f g)

/-- The original evaluation edge is recovered from the actual first triangle, including its seam. -/
theorem evaluation_native :
    PathLift (simplex f g) (edge (k := 4) 0 1) (evaluationComparison (f ≫ g)) := by
  have h := PathLift.trans_left _ (HomotopyLift.target _ (total_native f g))
  intro n s x
  exact h n s x

/-- Both actual Model-pasting halves retain their original equality transport. -/
theorem model_native :
    HomotopyLift (simplex f g) modelParameter (evaluationModelCompositionRelHomotopy f g) :=
  pasting_native (simplex f g) _ _ _ _ _ _ _ _ _ _
    (evaluationComposition_pasting f g) (total_native f g) (cut_native f g)

/-- The original ofLevels wrapper preserves the full Model-pasting surface. -/
theorem totalWhiskered_native :
    HomotopyLift (simplex f g) modelParameter (evaluationCompositionTotalWhiskered f g) := by
  intro n r s x
  exact model_native f g n r s x

/-- The actual binary triangle retains the unchanged outer evaluation half-clock. -/
theorem totalSplit_native :
    HomotopyLift (simplex f g) splitParameter (evaluationCompositionTotalSplit f g) := by
  have h := HomotopyLift.hcomp (simplex f g)
    (PathLift.refl _ (evaluation_native f g)) (normalization_native f g)
  intro n r s x
  exact h n r s x

/-- The entire selected global evaluation composition is the literal scalar word in one simplex. -/
theorem composition_native :
    HomotopyLift (simplex f g) compositionParameter (evaluationCompositionRelHomotopy f g) :=
  HomotopyLift.trans _ (HomotopyLift.symm _ (totalSplit_native f g))
    (totalWhiskered_native f g)

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputSimplex
