/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputLaurentFace
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputChartFaceSeams
public import
Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalBassEvaluationInputChartPostAttachment

/-!
# The full Laurent seams of the mixed evaluation cube

Both chart squares share the unchanged Laurent evaluation edge with its complete source and
cut nodes. These are equalities in the common-reference carrier, retaining every anchor.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.GlobalBassEvaluation.InputLaurentSeams
open GlobalSectionChangeIndex
variable {X Y : Scheme.{u}} (g : X ⟶ Y)
  (k : laurent ⟶ polynomial)
  (hk : ∀ Z, k.app Z ≫ projection.app Z = GlobalRawBass.laurentProjection.app Z)

/-- Both complete source nodes are the same strict mixed reference. -/
theorem source_node : InputChartSquareParameter.nodes g k hk 0 =
    InputLaurentFace.firstNodes (laurent.map g) (GlobalRawBass.laurentProjection.app Y) 0 :=
  InputChartFaceNodes.source_node g k hk

/-- Both complete cut nodes retain the actual Laurent evaluation isomorphism. -/
theorem cut_node : InputChartSquareParameter.nodes g k hk 3 =
    InputLaurentFace.firstNodes (laurent.map g) (GlobalRawBass.laurentProjection.app Y) 3 := by
  rw [InputChartFaceNodes.post_source_node, InputChartReference.post_nodes,
    InputChartSimplex.chartNodes_zero]
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  exact (congrArg (fun e => InputMixedDesc.postSourceIso g ≪≫ e)
    (isoWhiskerRight_refl (InputChartSimplex.sourceMap Y).functor
      (evaluationRawMap (laurent.map g)).functor)).trans
      (Iso.trans_refl _)

private def laurentFace : ⦋1⦌ ⟶ ⦋4⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 3], by decide⟩

private def chartFace : ⦋1⦌ ⟶ ⦋7⦌ :=
  SimplexCategory.Hom.mk ⟨![0, 3], by decide⟩

private theorem map_edge_scalar {p q : ℕ} (a : ⦋p⦌ ⟶ ⦋q⦌)
    (i j : Fin (p + 1)) (t : unitInterval) :
    StdSimplex.map a.toOrderHom ((SimplexParameters.edge i j) t) =
      SimplexParameters.edge (a.toOrderHom i) (a.toOrderHom j) t := map_edge a i j t

private theorem laurent_edge_scalar (r : unitInterval) :
    StdSimplex.map laurentFace.toOrderHom ((SimplexParameters.edge (k := 1) 0 1) r) =
      (SimplexParameters.edge (k := 4) 0 3) r := by
  simpa only [laurentFace, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one] using map_edge_scalar laurentFace 0 1 r

private theorem chart_edge_scalar (r : unitInterval) :
    StdSimplex.map chartFace.toOrderHom ((SimplexParameters.edge (k := 1) 0 1) r) =
      (SimplexParameters.edge (k := 7) 0 3) r := by
  simpa only [chartFace, SimplexCategory.Hom.toOrderHom_mk, OrderHom.coe_mk,
    Matrix.cons_val_zero, Matrix.cons_val_one] using map_edge_scalar chartFace 0 1 r

/-- The whole chart source edge is the original Laurent evaluation carrier path. -/
theorem edge (r : unitInterval) :
    InputChartSquareParameter.edge g k hk 0 3 r = InputLaurentFace.curve g r := by
  have h := CommonReferenceNerve.parameter_eq_of_face_nodes (InputMixedDesc.sourceMap g)
    (InputLaurentFace.firstNodes (laurent.map g) (GlobalRawBass.laurentProjection.app Y))
    (InputChartSquareParameter.nodes g k hk) laurentFace chartFace
    (fun i => by
      fin_cases i
      · exact source_node g k hk
      · exact cut_node g k hk) ((SimplexParameters.edge (k := 1) 0 1) r)
  change CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
    (InputChartSquareParameter.nodes g k hk) ((SimplexParameters.edge (k := 7) 0 3) r) =
      CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
        (InputLaurentFace.firstNodes (laurent.map g) (GlobalRawBass.laurentProjection.app Y))
        ((SimplexParameters.edge (k := 4) 0 3) r)
  exact (congrArg
    (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
      (InputChartSquareParameter.nodes g k hk)) (chart_edge_scalar r)).symm.trans
    (h.trans (congrArg
      (CommonReferenceNerve.parameter (InputMixedDesc.sourceMap g)
        (InputLaurentFace.firstNodes (laurent.map g) (GlobalRawBass.laurentProjection.app Y)))
      (laurent_edge_scalar r)))


/-- The positive chart source edge keeps the original independent Laurent time. -/
theorem plus_seam (r : unitInterval) :
    InputChartSquareParameter.plusParameter g (r, 0) =
      InputLaurentFace.parameter g (r, 0) := by
  rw [InputLaurentFace.parameter_apply]
  exact (InputChartSquareParameter.parameter_left g plus GlobalRawBass.plus_projection r).trans
    (edge g plus GlobalRawBass.plus_projection r)

/-- The inverse chart source edge is the same Laurent face at its other height endpoint. -/
theorem minus_seam (r : unitInterval) :
    InputChartSquareParameter.minusParameter g (r, 0) =
      InputLaurentFace.parameter g (r, 1) := by
  rw [InputLaurentFace.parameter_apply]
  exact (InputChartSquareParameter.parameter_left g minus GlobalRawBass.minus_projection r).trans
    (edge g minus GlobalRawBass.minus_projection r)

/-- The complete strict-source face is constant along its initial cylinder edge. -/
theorem pre_zero_constant (s : unitInterval) :
    InputMixedDesc.preSquareParameter g (0, s) =
      InputMixedDesc.preSquareParameter g (0, 0) := by
  change CommonReferenceNerve.mapParameter (InputMixedDesc.preNode g)
    (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X) (InputChartSimplex.nodes X)
      (collapsed InputChartSimplex.descParameter (0, s))) = _
  change _ = CommonReferenceNerve.mapParameter (InputMixedDesc.preNode g)
    (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X) (InputChartSimplex.nodes X)
      (collapsed InputChartSimplex.descParameter (0, 0)))
  exact congrArg (fun z => CommonReferenceNerve.mapParameter (InputMixedDesc.preNode g)
    (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap X)
      (InputChartSimplex.nodes X) z))
    ((collapsed_zero_path InputChartSimplex.descParameter s).trans
      (collapsed_zero_path InputChartSimplex.descParameter (0 : unitInterval)).symm)

/-- The complete postcomposed face is constant along its initial cylinder edge. -/
theorem post_zero_constant (s : unitInterval) :
    InputMixedDesc.postSquareParameter g (0, s) =
      InputMixedDesc.postSquareParameter g (0, 0) := by
  change CommonReferenceNerve.mapParameter (InputMixedDesc.postNode g)
    (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap Y) (InputChartSimplex.nodes Y)
      (collapsed InputChartSimplex.descParameter (0, s))) = _
  change _ = CommonReferenceNerve.mapParameter (InputMixedDesc.postNode g)
    (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap Y) (InputChartSimplex.nodes Y)
      (collapsed InputChartSimplex.descParameter (0, 0)))
  exact congrArg (fun z => CommonReferenceNerve.mapParameter (InputMixedDesc.postNode g)
    (CommonReferenceNerve.parameter (InputChartSimplex.sourceMap Y)
      (InputChartSimplex.nodes Y) z))
    ((collapsed_zero_path InputChartSimplex.descParameter s).trans
      (collapsed_zero_path InputChartSimplex.descParameter (0 : unitInterval)).symm)

/-- The whole F0/L0 edge agrees inside the carrier, including both original endpoints. -/
theorem source_face (s : unitInterval) :
    InputMixedDesc.preSquareParameter g (0, s) = InputLaurentFace.parameter g (0, s) := by
  rw [pre_zero_constant]
  exact (InputChartFaceSeams.pre_plus g 0).trans
    ((plus_seam g 0).trans (by rfl))

/-- The original postcomposed face begins at precisely the terminal Laurent evaluation node. -/
theorem post_source_face (s : unitInterval) :
    InputMixedDesc.postSquareParameter g (0, s) = InputLaurentFace.parameter g (1, s) := by
  rw [post_zero_constant, InputChartFaceSeams.post_plus]
  calc
    InputChartSquareParameter.edge g
        plus
        GlobalRawBass.plus_projection 3 4 0 =
      InputChartSquareParameter.edge g
        plus
        GlobalRawBass.plus_projection 0 3 1 := by
      rw [Path.source, Path.target]
    _ = InputLaurentFace.curve g 1 := edge g
      plus GlobalRawBass.plus_projection 1
    _ = InputLaurentFace.parameter g (1, s) := rfl

end Quillen.PerfectComplexes.GlobalBassEvaluation.InputLaurentSeams
