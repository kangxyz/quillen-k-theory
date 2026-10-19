/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputChartReference
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveReanchorFamily

/-!
# The original raw rectangle in the mixed Laurent reference

The proved chart projection equation reanchors the complete original rectangle without
changing any point of its native two-dimensional family or its selected normalization face.
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

/-- The original two-dimensional raw rectangle, with its complete mixed reference. -/
def rawParameter :=
  (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (rawNode g k hk)).comp
    DoubleSquareScalarPaths.rectangleParameter.toContinuousMap

/-- Every native point is the unchanged original geometric double-square comparison. -/
theorem raw_parameter_native (n : ℕ) (r s : unitInterval)
    (x : (prespectrum (globalModel.obj (op Y))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily (InputMixedDesc.sourceMap g)
      (rawParameter g k hk) n ((r, s), x) =
    (boundedFlatDoubleSquareTrackComparison (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g)).level n
        (r, (s, (prespectrumMap (evaluationModel (op Y))).map n x)) := by
  refine (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _ _
    (rawNode g k hk) (r, s) (DoubleSquareScalarPaths.rectangleParameter (r, s)) rfl n x).trans ?_
  have h := congrArg
    (fun F => F (DoubleSquareScalarPaths.rectangleParameter (r, s), x))
    (CommonReferenceNerve.prespectrumFamily_reanchor (chartSourceIso g k hk)
      (InputRectangleNodes.rawNode (projection.app Y) (k.app Y)
        (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
        (projection.naturality g) (k.naturality g)) n)
  refine h.trans ?_
  exact (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex
    (InputTripleNodes.sourceMap (laurent.map g) (k.app Y) (projection.app Y))
    (InputRectangleNodes.rawParameter (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g))
    (InputRectangleNodes.rawNode (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g)) (r, s)
    (DoubleSquareScalarPaths.rectangleParameter (r, s)) rfl n x).symm.trans
      (InputRectangleNodes.raw_parameter_native (projection.app Y) (k.app Y)
        (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
        (projection.naturality g) (k.naturality g) n r s x)

/-- The original total Y node is the full second raw rectangle node in the mixed reference. -/
theorem post_total_node : postNode g k hk 1 = rawNode g k hk 2 :=
  congrArg (fun N : InputTripleNodes.Node (laurent.map g) (k.app Y) (projection.app Y) =>
    (⟨N.1, chartSourceIso g k hk ≪≫ N.2⟩ : Node g))
    (InputRectangleNodes.post_total_node (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g))

/-- The actual geometric Y intermediate is the full third raw node. -/
theorem post_intermediate_node : postNode g k hk 2 = rawNode g k hk 3 :=
  congrArg (fun N : InputTripleNodes.Node (laurent.map g) (k.app Y) (projection.app Y) =>
    (⟨N.1, chartSourceIso g k hk ≪≫ N.2⟩ : Node g))
    (InputRectangleNodes.post_intermediate_node (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g))

/-- The original split Y target is exactly full raw rectangle node eleven. -/
theorem post_target_node : postNode g k hk 4 = rawNode g k hk 11 :=
  congrArg (fun N : InputTripleNodes.Node (laurent.map g) (k.app Y) (projection.app Y) =>
    (⟨N.1, chartSourceIso g k hk ≪≫ N.2⟩ : Node g))
    (InputRectangleNodes.post_target_node (projection.app Y) (k.app Y)
      (projection.app X) (k.app X) g (polynomial.map g) (laurent.map g)
      (projection.naturality g) (k.naturality g))

/-- The entire shared normalization characteristic face agrees before native evaluation. -/
theorem normalization_parameter (z : StdSimplex ℝ (Fin 3)) :
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (postNode g k hk)
      (StdSimplex.map (InputSimplex.triangleFace 1 2 4 (by decide) (by decide)).toOrderHom z) =
    CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g) (rawNode g k hk)
      (StdSimplex.map InputRectangleNodes.normalizationFace.toOrderHom z) := by
  apply CommonReferenceNerve.parameter_eq_of_face_nodes
  intro i
  fin_cases i
  · exact post_total_node g k hk
  · exact post_intermediate_node g k hk
  · exact post_target_node g k hk

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputChartReference
