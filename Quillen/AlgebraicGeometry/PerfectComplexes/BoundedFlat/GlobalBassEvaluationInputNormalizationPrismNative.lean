/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputNormalizationPrism
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.NativeBinaryComparison
public import Quillen.Waldhausen.SConstruction.Iterated.RealizationSimplexComposition
public import Quillen.Waldhausen.SConstruction.Iterated.ScalarRouteExtraction
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveParameter
public import Quillen.Topology.Realization.SimplexGridColumn

/-!
# The original three-parameter evaluation-normalization prism

The actual product-realization parameter keeps the evaluation time independent of both
original normalization comparison times. Its full native family, both whole rows, and all
three original evaluation columns retain their specified clocks.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum
open Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputNormalizationPrism
open GlobalSectionChangeIndex
variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- Repeating the terminal vertex extracts the unchanged first evaluation edge. -/
def firstTriangleFace : ⦋2⦌ ⟶ ⦋1⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 1, 1], by decide⟩

/-- The entire degenerate face uses the original evaluation transformation and identity. -/
theorem first_triangle_face : (firstSimplex h).face firstTriangleFace =
    ModelSimplex.triangle (F := firstSource h) (G := firstTarget h) (H := firstTarget h)
      (evaluationComparisonIso h).hom (𝟙 _)
      (fun _ => (modelOf (boundedFlatPerfectWaldhausen Z)).waldhausen.weq_iso _ inferInstance)
      (fun _ => (modelOf (boundedFlatPerfectWaldhausen Z)).waldhausen.weq_iso _ inferInstance) := by
  apply ModelSimplex.ofIsos_face_triangle
  · exact Category.id_comp _
  · exact Category.comp_id _

private theorem first_triangle_native :
    HomotopyLift (firstSimplex h) (triangle firstTriangleFace)
      (prespectrumTransformationCompositionHomotopy
        (F := firstSource h) (G := firstTarget h) (H := firstTarget h)
        (evaluationComparisonIso h).hom (𝟙 _)
        (fun _ => (modelOf (boundedFlatPerfectWaldhausen Z)).waldhausen.weq_iso _ inferInstance)
        (fun _ => (modelOf (boundedFlatPerfectWaldhausen Z)).waldhausen.weq_iso _ inferInstance)) :=
  triangle_lift _ _ _ _ _ _ (first_triangle_face h)

/-- Every point of the first factor is the original evaluation comparison, with no new pause. -/
theorem first_native :
    PathLift (firstSimplex h) (edge (k := 1) 0 1) (evaluationComparison h) := by
  have he := PathLift.trans_left _ (HomotopyLift.target _ (first_triangle_native h))
  intro n t x
  exact he n t x

/-- The actual product parameter keeps all three times independent. -/
def parameter : C(unitInterval × (unitInterval × unitInterval), StdSimplex ℝ (Fin 6)) :=
  ⟨fun z => Quillen.SimplexGrid.parameter.{u} 1 2
    ((edge (k := 1) 0 1) z.1, Quillen.TheoremB.compositionTriangleHomotopy z.2), by fun_prop⟩

/-- The initial evaluation face retains the entire original normalization parameter. -/
theorem parameter_evaluation_zero (r s : unitInterval) :
    parameter.{u} (0, (r, s)) =
      StdSimplex.map (Quillen.SimplexGrid.rowFace 1 2 0).toOrderHom
        (Quillen.TheoremB.compositionTriangleHomotopy (r, s)) := by
  change Quillen.SimplexGrid.parameter 1 2
    ((edge (k := 1) 0 1) 0, Quillen.TheoremB.compositionTriangleHomotopy (r, s)) = _
  rw [Path.source]
  exact Quillen.SimplexGrid.parameter_row 1 2 0 _

/-- The terminal evaluation face retains the same whole normalization parameter. -/
theorem parameter_evaluation_one (r s : unitInterval) :
    parameter.{u} (1, (r, s)) =
      StdSimplex.map (Quillen.SimplexGrid.rowFace 1 2 1).toOrderHom
        (Quillen.TheoremB.compositionTriangleHomotopy (r, s)) := by
  change Quillen.SimplexGrid.parameter 1 2
    ((edge (k := 1) 0 1) 1, Quillen.TheoremB.compositionTriangleHomotopy (r, s)) = _
  rw [Path.target]
  exact Quillen.SimplexGrid.parameter_row 1 2 1 _

/-- The direct normalization boundary keeps the independent evaluation time. -/
theorem parameter_normalization_zero (t s : unitInterval) :
    parameter.{u} (t, (0, s)) = Quillen.SimplexGrid.parameter.{u} 1 2
      ((edge (k := 1) 0 1) t, Quillen.TheoremB.triangleEdgePath 0 2 s) := by
  change Quillen.SimplexGrid.parameter 1 2
    ((edge (k := 1) 0 1) t, Quillen.TheoremB.compositionTriangleHomotopy (0, s)) = _
  rw [Quillen.TheoremB.compositionTriangleHomotopy.apply_zero]
  rfl

/-- The split normalization boundary keeps the original two-half concatenation clock. -/
theorem parameter_normalization_one (t s : unitInterval) :
    parameter.{u} (t, (1, s)) = Quillen.SimplexGrid.parameter.{u} 1 2
      ((edge (k := 1) 0 1) t,
        ((Quillen.TheoremB.triangleEdgePath 0 1).trans
          (Quillen.TheoremB.triangleEdgePath 1 2)) s) := by
  change Quillen.SimplexGrid.parameter 1 2
    ((edge (k := 1) 0 1) t, Quillen.TheoremB.compositionTriangleHomotopy (1, s)) = _
  rw [Quillen.TheoremB.compositionTriangleHomotopy.apply_one]
  rfl

private def binaryFamily (n : ℕ) :
    C(unitInterval × (unitInterval ×
      (prespectrum (modelOf (boundedFlatPerfectWaldhausen Z))).space n),
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen X))).space n) :=
  (prespectrumSimplexFamily (BinaryNormalizationSimplex.simplex f g) n).comp
    ⟨fun z => (Quillen.TheoremB.compositionTriangleHomotopy (z.1, z.2.1), z.2.2),
      by fun_prop⟩

private theorem binary_model_whole (n : ℕ) :
    binaryFamily f g n =
      ((prespectrumTransformationCompositionHomotopy
        (BinaryNormalizationSimplex.first f g).hom (BinaryNormalizationSimplex.second f g).hom
        (fun _ => (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _ inferInstance)
        (fun _ => (modelOf (boundedFlatPerfectWaldhausen X)).waldhausen.weq_iso _
          inferInstance)).level n).toContinuousMap := by
  apply ContinuousMap.ext
  rintro ⟨r, s, x⟩
  exact BinaryNormalizationSimplex.whole_triangle f g n r s x

private theorem binary_whole (n : ℕ) : binaryFamily f g n =
    ((boundedFlatNormalizedCompTrackComparison f g).level n).toContinuousMap :=
  (binary_model_whole f g n).trans (BinaryNormalizationSimplex.native_level f g n).symm

/-- The original moving evaluation input retains all three independent time coordinates. -/
def movingParameter (n : ℕ) :
    C((unitInterval × (unitInterval × unitInterval)) ×
      (prespectrum (globalModel.obj (op T))).space n,
        unitInterval × (unitInterval ×
          (prespectrum (modelOf (boundedFlatPerfectWaldhausen Z))).space n)) :=
  ⟨fun z => (z.1.2.1, (z.1.2.2, (evaluationComparison h).level n (z.1.1, z.2))),
    by fun_prop⟩

/-- The entire native family over the actual product-realization parameter. -/
def nativeFamily (n : ℕ) :=
  (prespectrumSimplexFamily (simplex f g h) n).comp
    (⟨fun z => (parameter.{u+1} z.1, z.2), by fun_prop⟩ :
      C((unitInterval × (unitInterval × unitInterval)) ×
        (prespectrum (globalModel.obj (op T))).space n, _))

private theorem model_whole (n : ℕ) :
    nativeFamily f g h n = (binaryFamily f g n).comp (movingParameter h n) := by
  apply ContinuousMap.ext
  rintro ⟨⟨t, r, s⟩, x⟩
  exact (congrArg
    (fun S => prespectrumSimplexFamily S n (parameter.{u+1} (t, (r, s)), x))
    (product_simplex f g h)).trans
      ((CommonReferenceProduct.prespectrum_comp (firstSource h) (firstVertices h) (firstAnchors h)
        (BinaryNormalizationSimplex.sourceMap f g) (binaryVertices f g) (binaryAnchors f g)
        n x ((edge (k := 1) 0 1) t) (Quillen.TheoremB.compositionTriangleHomotopy (r, s))).trans
        ((congrArg (fun S => prespectrumSimplexFamily S n
          (Quillen.TheoremB.compositionTriangleHomotopy (r, s),
            prespectrumSimplexFamily (firstSimplex h) n ((edge (k := 1) 0 1) t, x)))
          (binary_simplex f g)).trans
          (congrArg (fun y => prespectrumSimplexFamily (BinaryNormalizationSimplex.simplex f g) n
            (Quillen.TheoremB.compositionTriangleHomotopy (r, s), y)) (first_native h n t x))))

/-- Equality of the complete continuous families precedes evaluation of the original raw track. -/
theorem whole_native (n : ℕ) :
    nativeFamily f g h n =
      ((boundedFlatNormalizedCompTrackComparison f g).level n).toContinuousMap.comp
        (movingParameter h n) :=
  (model_whole f g h n).trans
    (congrArg (fun A => A.comp (movingParameter h n)) (binary_whole f g n))

/-- Every point of the first row is the original unconverted normalization triangle. -/
theorem pre_row_parameter (z : StdSimplex ℝ (Fin 3)) :
    CommonReferenceNerve.parameter (InputTripleNodes.sourceMap f g h) (nodes f g h)
      (Quillen.SimplexGrid.parameter.{u} 1 2 (StdSimplex.single 0, z)) =
    CommonReferenceNerve.parameter (InputTripleNodes.sourceMap f g h) (preNodes f g h) z := by
  refine (congrArg
    (CommonReferenceNerve.parameter (InputTripleNodes.sourceMap f g h) (nodes f g h))
    (Quillen.SimplexGrid.parameter_row 1 2 _ z)).trans ?_
  refine (CommonReferenceNerve.parameter_face (InputTripleNodes.sourceMap f g h)
    (nodes f g h) (Quillen.SimplexGrid.rowFace 1 2 _) z).trans ?_
  apply congrArg (fun N => CommonReferenceNerve.parameter (InputTripleNodes.sourceMap f g h) N z)
  funext i
  fin_cases i <;> rfl

/-- Every point of the second row retains the actual converted normalization references. -/
theorem converted_row_parameter (z : StdSimplex ℝ (Fin 3)) :
    CommonReferenceNerve.parameter (InputTripleNodes.sourceMap f g h) (nodes f g h)
      (Quillen.SimplexGrid.parameter.{u} 1 2 (StdSimplex.single 1, z)) =
    CommonReferenceNerve.parameter (InputTripleNodes.sourceMap f g h) (convertedNodes f g h) z := by
  refine (congrArg
    (CommonReferenceNerve.parameter (InputTripleNodes.sourceMap f g h) (nodes f g h))
    (Quillen.SimplexGrid.parameter_row 1 2 _ z)).trans ?_
  refine (CommonReferenceNerve.parameter_face (InputTripleNodes.sourceMap f g h)
    (nodes f g h) (Quillen.SimplexGrid.rowFace 1 2 _) z).trans ?_
  apply congrArg (fun N => CommonReferenceNerve.parameter (InputTripleNodes.sourceMap f g h) N z)
  funext i
  fin_cases i <;> rfl

/-- The original three vertical families are the actual right-whiskered evaluation comparison. -/
theorem column_native (j : Fin 3) (n : ℕ) (t : unitInterval)
    (x : (prespectrum (globalModel.obj (op T))).space n) :
    prespectrumSimplexFamily (simplex f g h) n
      (Quillen.SimplexGrid.parameter.{u} 1 2 ((edge (k := 1) 0 1) t, StdSimplex.single j), x) =
    (prespectrumMap (binaryVertices f g j)).map n ((evaluationComparison h).level n (t, x)) := by
  exact (congrArg (fun z => prespectrumSimplexFamily (simplex f g h) n (z, x))
    (Quillen.SimplexGrid.parameter_column 1 2 j ((edge (k := 1) 0 1) t))).trans
    ((prespectrumSimplexFamily_face (simplex f g h)
      (Quillen.SimplexGrid.columnFace 1 2 j) n ((edge (k := 1) 0 1) t) x).trans
      ((congrArg (fun S => prespectrumSimplexFamily S n ((edge (k := 1) 0 1) t, x))
        (column_face f g h j)).trans
        ((prespectrumSimplexFamily_postcomp (firstSimplex h) (binaryVertices f g j)
          n ((edge (k := 1) 0 1) t) x).trans
          (congrArg ((prespectrumMap (binaryVertices f g j)).map n) (first_native h n t x)))))

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputNormalizationPrism
