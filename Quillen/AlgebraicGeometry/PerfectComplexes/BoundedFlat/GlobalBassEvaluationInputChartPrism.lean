/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputChartParameters
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputChartRawFace
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputNormalizationPrismNative

/-!
# The actual normalization prism attached to the mixed chart reference

Both complete prism rows are identified before native evaluation: the first is the original
strict-precomposed chart normalization face, and the second is the converted raw rectangle
face. The actual evaluation bridges remain the vertical columns of the whole prism.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputChartReference
open GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- All six prism nodes retain both original square and chart reference transports. -/
def prismNode (i : Fin 6) : Node g :=
  ModelSimplex.reanchorNodes (chartSourceIso g k hk)
    (ModelSimplex.reanchorNodes
      (InputRectangleNodes.lastSourceIso (projection.app Y) (k.app Y)
        (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
        (projection.naturality g) (k.naturality g))
      (InputNormalizationPrism.nodes (k.app X) (projection.app X) g)) i

/-- The first complete prism row is the original strict-precomposed normalization face. -/
theorem prism_pre_nodes (i : Fin 3) :
    prismNode g k hk ((Quillen.SimplexGrid.rowFace 1 2 0).toOrderHom i) =
      preNode g k hk ((InputSimplex.triangleFace 1 2 4 (by decide) (by decide)).toOrderHom i) := by
  fin_cases i <;> rfl

/-- Only the converted second row agrees with the full original raw rectangle nodes. -/
theorem prism_raw_nodes (i : Fin 3) :
    prismNode g k hk ((Quillen.SimplexGrid.rowFace 1 2 1).toOrderHom i) =
      rawNode g k hk (InputRectangleNodes.preNormalizationFace.toOrderHom i) := by
  fin_cases i
  · exact congrArg
      (fun N : InputTripleNodes.Node (laurent.map g) (k.app Y) (projection.app Y) =>
        (⟨N.1, chartSourceIso g k hk ≪≫ N.2⟩ : Node g))
      (InputRectangleNodes.pre_total_node (projection.app Y) (k.app Y)
        (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
        (projection.naturality g) (k.naturality g))
  · exact congrArg
      (fun N : InputTripleNodes.Node (laurent.map g) (k.app Y) (projection.app Y) =>
        (⟨N.1, chartSourceIso g k hk ≪≫ N.2⟩ : Node g))
      (InputRectangleNodes.pre_intermediate_node (projection.app Y) (k.app Y)
        (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
        (projection.naturality g) (k.naturality g))
  · exact congrArg
      (fun N : InputTripleNodes.Node (laurent.map g) (k.app Y) (projection.app Y) =>
        (⟨N.1, chartSourceIso g k hk ≪≫ N.2⟩ : Node g))
      (InputRectangleNodes.pre_target_node (projection.app Y) (k.app Y)
        (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
        (projection.naturality g) (k.naturality g))

/-- The whole unconverted row is exactly its original five-node chart face. -/
theorem prism_pre_parameter (z : StdSimplex ℝ (Fin 3)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (prismNode g k hk)
      (Quillen.SimplexGrid.parameter.{u} 1 2 (StdSimplex.single 0, z)) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (preNode g k hk)
      (StdSimplex.map (InputSimplex.triangleFace 1 2 4 (by decide) (by decide)).toOrderHom z) := by
  exact (congrArg
    (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (prismNode g k hk))
    (Quillen.SimplexGrid.parameter_row 1 2 0 z)).trans
    (CommonReferenceNerve.parameter_eq_of_face_nodes (InputMixedDesc.sourceMap g)
      (preNode g k hk) (prismNode g k hk)
      (InputSimplex.triangleFace 1 2 4 (by decide) (by decide))
      (Quillen.SimplexGrid.rowFace 1 2 0) (prism_pre_nodes g k hk) z)

/-- The whole converted row is exactly the original raw normalization face. -/
theorem prism_raw_parameter (z : StdSimplex ℝ (Fin 3)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (prismNode g k hk)
      (Quillen.SimplexGrid.parameter.{u} 1 2 (StdSimplex.single 1, z)) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (rawNode g k hk)
      (StdSimplex.map InputRectangleNodes.preNormalizationFace.toOrderHom z) := by
  exact (congrArg
    (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (prismNode g k hk))
    (Quillen.SimplexGrid.parameter_row 1 2 1 z)).trans
    (CommonReferenceNerve.parameter_eq_of_face_nodes (InputMixedDesc.sourceMap g)
      (rawNode g k hk) (prismNode g k hk) InputRectangleNodes.preNormalizationFace
      (Quillen.SimplexGrid.rowFace 1 2 1) (prism_raw_nodes g k hk) z)

/-- The entire actual bridge prism is a compact parameter in the mixed Laurent nerve. -/
def prismParameter :=
  (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (prismNode g k hk)).comp
    InputNormalizationPrism.parameter.{u+1}

private theorem mixed_whole (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (prismParameter g k hk) n =
    InputNormalizationPrism.nativeFamily (k.app X) (projection.app X) g n := by
  apply ContinuousMap.ext
  rintro ⟨⟨t, r, s⟩, x⟩
  let N := InputNormalizationPrism.nodes (k.app X) (projection.app X) g
  let e := InputRectangleNodes.lastSourceIso (projection.app Y) (k.app Y)
    (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
    (projection.naturality g) (k.naturality g)
  let z := InputNormalizationPrism.parameter.{u+1} (t, (r, s))
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ _
    (prismNode g k hk) (t, (r, s)) z rfl n x).trans ?_
  exact (congrArg (fun F => F (z, x))
    (CommonReferenceNerve.prespectrumFamily_reanchor (chartSourceIso g k hk)
      (ModelSimplex.reanchorNodes e N) n)).trans
    ((congrArg (fun F => F (z, x))
      (CommonReferenceNerve.prespectrumFamily_reanchor e N n)).trans
      (congrArg (fun F => F (z, x))
        (CommonReferenceNerve.prespectrumFamily_eq
          (InputTripleNodes.sourceMap (k.app X) (projection.app X) g) N n)))

/-- The entire three-parameter continuous family is the unchanged original moving normalization. -/
theorem prism_whole_native (n : ℕ) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (prismParameter g k hk) n =
      ((boundedFlatNormalizedCompTrackComparison
        (k.app X) (projection.app X)).level n).toContinuousMap.comp
          (InputNormalizationPrism.movingParameter g n) :=
  (mixed_whole g k hk n).trans
    (InputNormalizationPrism.whole_native (k.app X) (projection.app X) g n)

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputChartReference
