/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Naturality

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPrisms
public import Quillen.Topology.Realization.SimplexGridProductFaces
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceProductNodes

/-!
# Full-reference endpoints of the actual ninety-node correction prisms

Every attachment retains the complete dependent nodes and actual canonical source anchors.
Only the sixteen original primitive product supports may be used for parameter restrictions.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeNerve
open BassReferenceMerge BassH0Merge BassH1Join
attribute [local irreducible] boundedFlatNormalizedPullback


private theorem product_first_reanchor {V W T : Model.{u}} {p q : ℕ}
    (F : V ⟶ T) (F₀ F₁ : V ⟶ W) (G₀ : W ⟶ T)
    (N : Fin (p + 1) → CommonReferenceNerve.Node F₁)
    (M : Fin (q + 1) → CommonReferenceNerve.Node G₀)
    (θ : F₀.functor ≅ F₁.functor) (η : F.functor ≅ (F₀ ≫ G₀).functor)
    (i : Fin (p + 1)) (j : Fin (q + 1)) :
    reanchoredProductNode F F₀ (fun i ↦ (N i).1) (fun i ↦ θ ≪≫ (N i).2)
      G₀ (fun j ↦ (M j).1) (fun j ↦ (M j).2) η (Quillen.SimplexGrid.index p q (i, j)) =
    reanchoredProductNode F F₁ (fun i ↦ (N i).1) (fun i ↦ (N i).2)
      G₀ (fun j ↦ (M j).1) (fun j ↦ (M j).2)
      (η ≪≫ isoWhiskerRight θ G₀.functor) (Quillen.SimplexGrid.index p q (i, j)) := by
  unfold reanchoredProductNode CommonReferenceProduct.vertices CommonReferenceProduct.references
  rw [Quillen.SimplexGrid.decode_index]
  dsimp only
  simp only [composition_pair_iso, isoWhiskerRight_trans, Iso.trans_assoc]

private theorem product_second_reanchor {V W T : Model.{u}} {p q : ℕ}
    (F : V ⟶ T) (F₀ : V ⟶ W) (G₀ G₁ : W ⟶ T)
    (N : Fin (p + 1) → CommonReferenceNerve.Node F₀)
    (M : Fin (q + 1) → CommonReferenceNerve.Node G₁)
    (θ : G₀.functor ≅ G₁.functor) (η : F.functor ≅ (F₀ ≫ G₀).functor)
    (i : Fin (p + 1)) (j : Fin (q + 1)) :
    reanchoredProductNode F F₀ (fun i ↦ (N i).1) (fun i ↦ (N i).2)
      G₀ (fun j ↦ (M j).1) (fun j ↦ θ ≪≫ (M j).2) η (Quillen.SimplexGrid.index p q (i, j)) =
    reanchoredProductNode F F₀ (fun i ↦ (N i).1) (fun i ↦ (N i).2)
      G₁ (fun j ↦ (M j).1) (fun j ↦ (M j).2)
      (η ≪≫ isoWhiskerLeft F₀.functor θ) (Quillen.SimplexGrid.index p q (i, j)) := by
  unfold reanchoredProductNode CommonReferenceProduct.vertices CommonReferenceProduct.references
  rw [Quillen.SimplexGrid.decode_index]
  dsimp only
  simp only [composition_pair_iso_other, isoWhiskerLeft_trans, Iso.trans_assoc]

private def productRow (r : Fin 3) : Fin 5 → Fin 18 :=
  ![CoefficientMovingSquareRows.outerRow, CoefficientMovingSquareRows.firstRow,
    CoefficientMovingSquareRows.secondRow] r

private def productRowEdge (r : Fin 3) (i : Fin 4) : ⦋1⦌ ⟶ ⦋17⦌ :=
  SimplexCategory.Hom.mk ⟨productRow r ∘ (BassH1Support.edgeFace i).toOrderHom,
    CoefficientMovingSquareRows.primitive_rows_monotone r i⟩

private def firstProductRow (r : Fin 3) (k : Fin 25) : Fin 90 :=
  Quillen.SimplexGrid.index 17 4
    (productRow r ((Quillen.SimplexGrid.indexEquiv 4 4).symm k).1,
      ((Quillen.SimplexGrid.indexEquiv 4 4).symm k).2)

private def secondProductRow (r : Fin 3) (k : Fin 25) : Fin 90 :=
  Quillen.SimplexGrid.index 4 17
    (((Quillen.SimplexGrid.indexEquiv 4 4).symm k).1,
      productRow r ((Quillen.SimplexGrid.indexEquiv 4 4).symm k).2)

private def firstProductFace (r : Fin 3) (i j : Fin 4) : ⦋3⦌ ⟶ ⦋89⦌ :=
  SimplexCategory.Hom.mk ⟨firstProductRow r ∘ (BassH1Support.edgePairFace i j).toOrderHom,
    (by decide : ∀ (r : Fin 3) (i j : Fin 4), Monotone
      (firstProductRow r ∘ (BassH1Support.edgePairFace i j).toOrderHom)) r i j⟩

private def secondProductFace (r : Fin 3) (i j : Fin 4) : ⦋3⦌ ⟶ ⦋89⦌ :=
  SimplexCategory.Hom.mk ⟨secondProductRow r ∘ (BassH1Support.edgePairFace i j).toOrderHom,
    (by decide : ∀ (r : Fin 3) (i j : Fin 4), Monotone
      (secondProductRow r ∘ (BassH1Support.edgePairFace i j).toOrderHom)) r i j⟩

private theorem first_product_face_index (r : Fin 3) (i j : Fin 4) (k l : Fin 2) :
    (firstProductFace r i j).toOrderHom (Quillen.SimplexGrid.index 1 1 (k, l)) =
      Quillen.SimplexGrid.index 17 4
        ((productRowEdge r i).toOrderHom k, (BassH1Support.edgeFace j).toOrderHom l) := by
  change firstProductRow r
    ((BassH1Support.edgePairFace i j).toOrderHom (Quillen.SimplexGrid.index 1 1 (k, l))) = _
  rw [BassH1Support.edgePair_index]
  unfold firstProductRow
  rw [Quillen.SimplexGrid.decode_index]
  rfl

private theorem second_product_face_index (r : Fin 3) (i j : Fin 4) (k l : Fin 2) :
    (secondProductFace r i j).toOrderHom (Quillen.SimplexGrid.index 1 1 (k, l)) =
      Quillen.SimplexGrid.index 4 17
        ((BassH1Support.edgeFace i).toOrderHom k, (productRowEdge r j).toOrderHom l) := by
  change secondProductRow r
    ((BassH1Support.edgePairFace i j).toOrderHom (Quillen.SimplexGrid.index 1 1 (k, l))) = _
  rw [BassH1Support.edgePair_index]
  unfold secondProductRow
  rw [Quillen.SimplexGrid.decode_index]
  rfl

private theorem first_product_parameter {V W : Model.{u}} (F : V ⟶ W)
    (N : Fin 90 → CommonReferenceNerve.Node F) (r : Fin 3) (s t : unitInterval) :
    CommonReferenceNerve.parameter F N (Quillen.SimplexGrid.parameter.{u} 17 4
      (StdSimplex.map (productRow r) (NativeSquareFiveSimplex.parameter s),
        NativeSquareFiveSimplex.parameter t)) =
    CommonReferenceNerve.parameter F (fun k ↦ N (firstProductRow r k))
      (Quillen.SimplexGrid.parameter.{u} 4 4
        (NativeSquareFiveSimplex.parameter s, NativeSquareFiveSimplex.parameter t)) := by
  obtain ⟨i, z, hz⟩ := BassH1Support.square_path_in s
  obtain ⟨j, w, hw⟩ := BassH1Support.square_path_in t
  rw [← hz, ← hw, ← StdSimplex.map_comp]
  change CommonReferenceNerve.parameter F N
    (Quillen.SimplexGrid.parameter.{u} 17 4
      (StdSimplex.map (productRowEdge r i).toOrderHom z,
        StdSimplex.map (BassH1Support.edgeFace j).toOrderHom w)) = _
  rw [Quillen.SimplexGrid.parameter_productMap (productRowEdge r i)
    (BassH1Support.edgeFace j) (firstProductFace r i j) (first_product_face_index r i j),
    BassH1Support.parameter_edgeProduct]
  exact (CommonReferenceNerve.parameter_face F N (firstProductFace r i j) _).trans
    (CommonReferenceNerve.parameter_face F (fun k ↦ N (firstProductRow r k))
      (BassH1Support.edgePairFace i j) _).symm

private theorem second_product_parameter {V W : Model.{u}} (F : V ⟶ W)
    (N : Fin 90 → CommonReferenceNerve.Node F) (r : Fin 3) (s t : unitInterval) :
    CommonReferenceNerve.parameter F N (Quillen.SimplexGrid.parameter.{u} 4 17
      (NativeSquareFiveSimplex.parameter s,
        StdSimplex.map (productRow r) (NativeSquareFiveSimplex.parameter t))) =
    CommonReferenceNerve.parameter F (fun k ↦ N (secondProductRow r k))
      (Quillen.SimplexGrid.parameter.{u} 4 4
        (NativeSquareFiveSimplex.parameter s, NativeSquareFiveSimplex.parameter t)) := by
  obtain ⟨i, z, hz⟩ := BassH1Support.square_path_in s
  obtain ⟨j, w, hw⟩ := BassH1Support.square_path_in t
  rw [← hz, ← hw, ← StdSimplex.map_comp]
  change CommonReferenceNerve.parameter F N
    (Quillen.SimplexGrid.parameter.{u} 4 17
      (StdSimplex.map (BassH1Support.edgeFace i).toOrderHom z,
        StdSimplex.map (productRowEdge r j).toOrderHom w)) = _
  rw [Quillen.SimplexGrid.parameter_productMap (BassH1Support.edgeFace i)
    (productRowEdge r j) (secondProductFace r i j) (second_product_face_index r i j),
    BassH1Support.parameter_edgeProduct]
  exact (CommonReferenceNerve.parameter_face F N (secondProductFace r i j) _).trans
    (CommonReferenceNerve.parameter_face F (fun k ↦ N (secondProductRow r k))
      (BassH1Support.edgePairFace i j) _).symm

universe v
private theorem plus_component_parameter {V W : Model.{v}} (F : V ⟶ W)
    (N : Fin 140 → CommonReferenceNerve.Node F) (s t : unitInterval) :
    CommonReferenceNerve.parameter F N (BassMWhole.scalarCube.{u} ![1, upper s, lower t]) =
      CommonReferenceNerve.parameter F
        (fun i ↦ N (BassMWholeOrder.oldIndex (BassH1Order.plusProductIndex i)))
        (BassH1Components.plusParameter.{u} (s, t)) := by
  rw [BassMWhole.cube_one]
  change CommonReferenceNerve.parameter F N
    (StdSimplex.map BassMWholeOrder.oldIndex
      (BassH1Order.h1Parameter.{u} (upper s, lower t))) = _
  rw [BassH1Order.h1_plus_cell]
  change CommonReferenceNerve.parameter F N
    (StdSimplex.map BassMWholeOrder.oldIndex
      (StdSimplex.map BassH1Order.plusProductIndex (BassH1Components.plusParameter.{u} (s, t)))) = _
  rw [← StdSimplex.map_comp]
  obtain ⟨i, j, z, hz⟩ := BassH1Support.plus_support.{u} s t
  rw [← hz]
  exact CommonReferenceNerve.parameter_supported F _ _
    (BassMWholeOrder.oldIndex ∘ BassH1Order.plusProductIndex) (fun _ ↦ rfl)
    (BassH1Support.edgePairFace i j) (BassMWholeOrder.oldPlusProduct_monotone i j) z

private theorem minus_component_parameter {V W : Model.{v}} (F : V ⟶ W)
    (N : Fin 140 → CommonReferenceNerve.Node F) (s t : unitInterval) :
    CommonReferenceNerve.parameter F N
      (BassMWhole.scalarCube.{u} ![1, upper s, upper (upper t)]) =
      CommonReferenceNerve.parameter F
        (fun i ↦ N (BassMWholeOrder.oldIndex (BassH1Order.minusProductIndex i)))
        (BassH1Components.minusParameter.{u} (s, t)) := by
  rw [BassMWhole.cube_one]
  change CommonReferenceNerve.parameter F N
    (StdSimplex.map BassMWholeOrder.oldIndex
      (BassH1Order.h1Parameter.{u} (upper s, upper (upper t)))) = _
  rw [BassH1Order.h1_minus_cell]
  change CommonReferenceNerve.parameter F N
    (StdSimplex.map BassMWholeOrder.oldIndex
      (StdSimplex.map BassH1Order.minusProductIndex
        (BassH1Components.minusParameter.{u} (s, t)))) = _
  rw [← StdSimplex.map_comp]
  obtain ⟨i, j, z, hz⟩ := BassH1Support.minus_support.{u} s t
  rw [← hz]
  exact CommonReferenceNerve.parameter_supported F _ _
    (BassMWholeOrder.oldIndex ∘ BassH1Order.minusProductIndex) (fun _ ↦ rfl)
    (BassH1Support.edgePairFace i j) (BassMWholeOrder.oldMinusProduct_monotone i j) z

private theorem row_first_anchor_small {A B C A' B' C' : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) (p' : B' ⟶ A') (q' : C' ⟶ B')
    (a : A' ⟶ A) (b : B' ⟶ B) (c : C' ⟶ C)
    (hp : b ≫ p = p' ≫ a) (hq : c ≫ q = q' ≫ b) :
    CoefficientMovingSquareRows.firstAnchor p q p' q' a b c hp hq =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        ((DoubleSquareTrack.total_eq p q p' q' a b c hp hq).symm.trans
          (Category.assoc q' p' a))) ≪≫
        boundedFlatNormalizedPullbackCompIso q' (p' ≫ a)) :=
  (smallIso_trans _ _).symm

private theorem row_second_anchor_small {A B C C' : Scheme.{u}}
    (p : B ⟶ A) (q : C ⟶ B) {B' : Scheme.{u}} (q' : C' ⟶ B')
    (b : B' ⟶ B) (c : C' ⟶ C) (hq : c ≫ q = q' ≫ b) :
    CoefficientMovingSquareRows.secondAnchor p q q' b c hq =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        ((DoubleSquareTrack.middle_eq p q q' b c hq).symm.trans
          (Category.assoc q' b p).symm)) ≪≫
        boundedFlatNormalizedPullbackCompIso (q' ≫ b) p) := by
  change smallIso _ ≪≫ smallIso (_ ≪≫ _) = _
  rw [← smallIso_trans, ← Iso.trans_assoc, eqToIso_trans]

private theorem product_node_index {V W T : Model.{u}} {p q : ℕ}
    (F : V ⟶ T) (H : V ⟶ W) (G : W ⟶ T)
    (N : Fin (p + 1) → CommonReferenceNerve.Node H)
    (M : Fin (q + 1) → CommonReferenceNerve.Node G)
    (η : F.functor ≅ (H ≫ G).functor) (i : Fin (p + 1)) (j : Fin (q + 1)) :
    reanchoredProductNode F H (fun k ↦ (N k).1) (fun k ↦ (N k).2)
      G (fun k ↦ (M k).1) (fun k ↦ (M k).2) η
      (Quillen.SimplexGrid.index p q (i, j)) = CommonReferenceProduct.node F H G η (N i) (M j) := by
  unfold reanchoredProductNode CommonReferenceProduct.vertices CommonReferenceProduct.references
  rw [Quillen.SimplexGrid.decode_index]
  rfl

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The direct polynomial source retains the actual original composite coefficient map. -/
theorem polynomialDirectTotal :
    polynomialProjection P c ≫ coefficientMap P v ≫ coefficientMap P u =
      coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)) ≫ polynomialProjection P a :=
  ((AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
    (polynomialUnderCoefficient R) (u ≫ v)).trans
    (congrArg (fun k ↦ polynomialProjection P c ≫ k) (coefficientMap_comp P u v))).symm

/-- The corresponding full reference transport uses that exact equality. -/
def polynomialDirectAnchor :
    (movingSquareSource P (polynomialUnderCoefficient R) u v).functor ≅
      (CoefficientSquareFamilies.polynomialSource P (u ≫ v)).functor :=
  eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (polynomialDirectTotal P u v)))

/-- Every direct polynomial row node retains the actual composite-map casts and reference. -/
theorem polynomial_direct_nodes (i : Fin 5) :
    movingSquareNodes P (polynomialUnderCoefficient R) u v
      (CoefficientMovingSquareRows.outerRow i) =
      anchorNode (polynomialDirectAnchor P u v)
        (CoefficientSquareFamilies.polynomialNodes P (u ≫ v) i) :=
  CoefficientMovingSquareRows.outer_row_nodes_cast _ _ _ _ _ _ _ _ _ _ _
    (coefficientMap_comp P u v) (BassH0Merge.polynomial_composite P u v)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (polynomialUnderCoefficient R) (u ≫ v)) i

variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)

/-- The direct chart source retains both original functor-applied composite maps. -/
theorem chartDirectTotal :
    coefficientMap P (α.app c) ≫ coefficientMap P ((polynomialUnderFunctor R).map v) ≫
      coefficientMap P ((polynomialUnderFunctor R).map u) =
    coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)) ≫ coefficientMap P (α.app a) :=
  ((AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α (u ≫ v)).trans
    (congrArg (fun k ↦ coefficientMap P (α.app c) ≫ k)
      (BassH0Merge.polynomial_composite P u v))).symm

/-- This is the actual source transport for the direct whole chart row. -/
def chartDirectAnchor : (movingSquareSource P α u v).functor ≅
    (CoefficientSquareFamilies.chartSource P (u ≫ v) α).functor :=
  eqToIso (congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (chartDirectTotal P u v α)))

/-- Every direct chart row node retains both raw intermediates and complete references. -/
theorem chart_direct_nodes (i : Fin 5) :
    movingSquareNodes P α u v (CoefficientMovingSquareRows.outerRow i) =
      anchorNode (chartDirectAnchor P u v α)
        (CoefficientSquareFamilies.chartNodes P (u ≫ v) α i) :=
  CoefficientMovingSquareRows.outer_row_nodes_cast _ _ _ _ _ _ _ _ _ _ _
    (BassH0Merge.polynomial_composite P u v) (BassH0Merge.laurent_composite P u v)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α (u ≫ v)) i

/-- The first original polynomial row retains its postcomposition anchor. -/
def polynomialFirstAnchor : (movingSquareSource P (polynomialUnderCoefficient R) u v).functor ≅
    (CoefficientSquareFamilies.polynomialSource P u ≫
      coefficientModel P ((polynomialUnderFunctor R).map v)).functor :=
  CoefficientMovingSquareRows.firstAnchor
    (coefficientMap P u) (coefficientMap P v)
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (polynomialUnderCoefficient R) u).symm
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (polynomialUnderCoefficient R) v).symm

/-- The second original polynomial row retains its precomposition anchor. -/
def polynomialSecondAnchor : (movingSquareSource P (polynomialUnderCoefficient R) u v).functor ≅
    (coefficientModel P u ≫ CoefficientSquareFamilies.polynomialSource P v).functor :=
  CoefficientMovingSquareRows.secondAnchor
    (coefficientMap P u) (coefficientMap P v)
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (polynomialProjection P b) (polynomialProjection P c)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (polynomialUnderCoefficient R) v).symm

/-- The first original chart row has its literal Laurent postcomposition reference. -/
def chartFirstAnchor : (movingSquareSource P α u v).functor ≅
    (CoefficientSquareFamilies.chartSource P u α ≫
      coefficientModel P ((laurentUnderFunctor R).map v)).functor :=
  CoefficientMovingSquareRows.firstAnchor
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map v))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α u).symm
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v).symm

/-- The second original chart row retains its polynomial precomposition reference. -/
def chartSecondAnchor : (movingSquareSource P α u v).functor ≅
    (coefficientModel P ((polynomialUnderFunctor R).map u) ≫
      CoefficientSquareFamilies.chartSource P v α).functor :=
  CoefficientMovingSquareRows.secondAnchor
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (coefficientMap P ((laurentUnderFunctor R).map v))
    (coefficientMap P (α.app b)) (coefficientMap P (α.app c))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v).symm

/-- All five first-row polynomial nodes retain their complete postcomposed references. -/
theorem polynomial_first_nodes (i : Fin 5) :
    movingSquareNodes P (polynomialUnderCoefficient R) u v
      (CoefficientMovingSquareRows.firstRow i) =
      postReferenceNode _ (coefficientModel P ((polynomialUnderFunctor R).map v))
        (polynomialFirstAnchor P u v) (CoefficientSquareFamilies.polynomialNodes P u i) :=
  CoefficientMovingSquareRows.first_row_nodes _ _ _ _ _ _ _ _ _ i

/-- All five second-row polynomial nodes retain their complete precomposed references. -/
theorem polynomial_second_nodes (i : Fin 5) :
    movingSquareNodes P (polynomialUnderCoefficient R) u v
      (CoefficientMovingSquareRows.secondRow i) =
      preReferenceNode _ (coefficientModel P u) (polynomialSecondAnchor P u v)
        (CoefficientSquareFamilies.polynomialNodes P v i) :=
  CoefficientMovingSquareRows.second_row_nodes _ _ _ _ _ _ _ _ _ i

/-- Every first-row chart node is the actual Laurent-postcomposed chart node. -/
theorem chart_first_nodes (i : Fin 5) :
    movingSquareNodes P α u v (CoefficientMovingSquareRows.firstRow i) =
      postReferenceNode _ (coefficientModel P ((laurentUnderFunctor R).map v))
        (chartFirstAnchor P u v α) (CoefficientSquareFamilies.chartNodes P u α i) :=
  CoefficientMovingSquareRows.first_row_nodes _ _ _ _ _ _ _ _ _ i

/-- Every second-row chart node is the actual polynomial-precomposed chart node. -/
theorem chart_second_nodes (i : Fin 5) :
    movingSquareNodes P α u v (CoefficientMovingSquareRows.secondRow i) =
      preReferenceNode _ (coefficientModel P ((polynomialUnderFunctor R).map u))
        (chartSecondAnchor P u v α) (CoefficientSquareFamilies.chartNodes P v α i) :=
  CoefficientMovingSquareRows.second_row_nodes _ _ _ _ _ _ _ _ _ i

variable {d : Under R} (w : c ⟶ d)

/-- The entire source product has exactly the left cube's original chart anchor. -/
theorem polynomial_product_source_anchor
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    polynomialProductAnchor P u v w α hc ≪≫ isoWhiskerRight (polynomialDirectAnchor P u v)
      (CoefficientSquareFamilies.chartSource P w α).functor =
      h0Anchor P (u ≫ v) w ≪≫ BassH1References.chartIso P (u ≫ v) w α hc := by
  have hD : polynomialDirectAnchor P u v =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        (polynomialDirectTotal P u v))) := (smallIso_eqToIso _).symm
  rw [polynomialProductAnchor, hD, h0_anchor_small, BassH1References.chartIso]
  erw [smallIso_postcomp, ← smallIso_trans, ← smallIso_trans]
  apply congrArg smallIso
  rw [← Iso.trans_assoc, eqToIso_trans]
  exact anchored_target_transport
    (coefficientMap P ((laurentUnderFunctor R).map w) ≫ coefficientMap P (α.app c))
    (polynomialDirectTotal P u v) _ (polynomialProductTotal P u v w α hc).symm
    ((BassH0Merge.total P (u ≫ v) w).trans (BassH1References.chart_total P (u ≫ v) w α hc).symm)

/-- The other source product has the right cube's specified original associativity anchor. -/
theorem chart_product_source_anchor
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d) :
    chartProductAnchor P u v w α hd ≪≫ isoWhiskerLeft
      (CoefficientSquareFamilies.polynomialSource P u).functor (chartDirectAnchor P v w α) =
      rightStartingAnchor P u v w ≪≫ BassH1References.chartIso P u (v ≫ w) α hb := by
  have hD : chartDirectAnchor P v w α =
      smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
        (chartDirectTotal P v w α))) := (smallIso_eqToIso _).symm
  rw [chartProductAnchor, hD, right_starting_anchor_h0, h0_anchor_small,
    BassH1References.chartIso]
  erw [smallIso_precomp, ← smallIso_trans, ← smallIso_trans]
  apply congrArg smallIso
  rw [← Iso.trans_assoc, eqToIso_trans]
  exact anchored_source_transport (chartDirectTotal P v w α)
    (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a) _
    (chartProductTotal P u v w α hd).symm
    ((BassH0Merge.total P u (v ≫ w)).trans (BassH1References.chart_total P u (v ≫ w) α hb).symm)

/-- The entire second polynomial row has the exact prewhiskered cube chart anchor. -/
theorem polynomial_product_target_anchor
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    polynomialProductAnchor P u v w α hc ≪≫
      isoWhiskerRight (polynomialSecondAnchor P u v)
        (CoefficientSquareFamilies.chartSource P w α).functor =
      precompAnchor P u v w ≪≫ isoWhiskerLeft (coefficientModel P u).functor
        (BassH1References.chartIso P v w α hc) := by
  rw [polynomialProductAnchor, polynomialSecondAnchor, row_second_anchor_small,
    precomp_anchor_small, BassH1References.chartIso]
  erw [smallIso_postcomp, smallIso_precomp]
  have hp : coefficientMap P ((polynomialUnderFunctor R).map v) ≫
      polynomialProjection P b = polynomialProjection P c ≫ coefficientMap P v :=
    AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (polynomialUnderCoefficient R) v
  have hraw := (anchored_factorizations_strict
    (coefficientMap P ((laurentUnderFunctor R).map w) ≫ coefficientMap P (α.app c))
    (coefficientMap P ((polynomialUnderFunctor R).map v) ≫ polynomialProjection P b)
    (coefficientMap P u)
    (laurentProjection P d ≫ coefficientMap P w ≫ coefficientMap P v)
    (polynomialProjection P c ≫ coefficientMap P v ≫ coefficientMap P u) _
    (BassH1References.chart_total P v w α hc).symm
    (by simpa only [Category.assoc] using
      congrArg (fun k ↦ k ≫ coefficientMap P u) hp.symm)
    (precomp_total P u v w) (polynomialProductTotal P u v w α hc).symm).symm
  simpa only [smallIso_trans, Iso.trans_assoc] using congrArg smallIso hraw

/-- The first chart row has exactly the postwhiskered cube's canonical chart reference. -/
theorem chart_product_target_anchor
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d) :
    chartProductAnchor P u v w α hd ≪≫
      isoWhiskerLeft (CoefficientSquareFamilies.polynomialSource P u).functor
        (chartFirstAnchor P v w α) =
      postcompAnchor P u v w ≪≫ isoWhiskerRight (BassH1References.chartIso P u v α hb)
        (coefficientModel P ((laurentUnderFunctor R).map w)).functor := by
  rw [chartProductAnchor, chartFirstAnchor, row_first_anchor_small,
    postcomp_anchor_small, BassH1References.chartIso]
  erw [smallIso_precomp, smallIso_postcomp]
  have hv := AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v
  have hw := AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α w
  have hraw := anchored_factorizations_strict
    (coefficientMap P ((laurentUnderFunctor R).map w))
    (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
    (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a)
    (coefficientMap P (α.app d) ≫ coefficientMap P ((polynomialUnderFunctor R).map w) ≫
      coefficientMap P ((polynomialUnderFunctor R).map v))
    (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u) _
    (by
      simpa only [Category.assoc, ← hv] using
        (congrArg (fun k ↦ k ≫ coefficientMap P ((polynomialUnderFunctor R).map v)) hw.symm))
    (BassH1References.chart_total P u v α hb).symm
    (chartProductTotal P u v w α hd).symm (postcomp_total P u v w)
  simpa only [smallIso_trans, Iso.trans_assoc] using congrArg smallIso hraw

/-- The middle product seam retains both actual factorizations and their strict associator. -/
theorem product_middle_anchor
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d) :
    polynomialProductAnchor P u v w α hc ≪≫
      isoWhiskerRight (polynomialFirstAnchor P u v)
        (CoefficientSquareFamilies.chartSource P w α).functor =
      chartProductAnchor P u v w α hd ≪≫
        isoWhiskerLeft (CoefficientSquareFamilies.polynomialSource P u).functor
          (chartSecondAnchor P v w α) := by
  rw [polynomialProductAnchor, polynomialFirstAnchor, row_first_anchor_small,
    chartProductAnchor, chartSecondAnchor, row_second_anchor_small]
  erw [smallIso_postcomp, smallIso_precomp]
  have hu : coefficientMap P ((polynomialUnderFunctor R).map u) ≫
      polynomialProjection P a = polynomialProjection P b ≫ coefficientMap P u :=
    AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (polynomialUnderCoefficient R) u
  have hv : coefficientMap P ((polynomialUnderFunctor R).map v) ≫
      polynomialProjection P b = polynomialProjection P c ≫ coefficientMap P v :=
    AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (polynomialUnderCoefficient R) v
  have hraw := (anchored_factorizations_strict
    (coefficientMap P ((laurentUnderFunctor R).map w) ≫ coefficientMap P (α.app c))
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a)
    (coefficientMap P (α.app d) ≫ coefficientMap P ((polynomialUnderFunctor R).map w) ≫
      coefficientMap P ((polynomialUnderFunctor R).map v))
    (polynomialProjection P c ≫ coefficientMap P v ≫ coefficientMap P u) _
    (by
      rw [AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α w,
        Category.assoc])
    (by
      simpa only [Category.assoc, hu] using
        (congrArg (fun k ↦ k ≫ coefficientMap P u) hv.symm))
    (chartProductTotal P u v w α hd).symm (polynomialProductTotal P u v w α hc).symm).symm
  simpa only [smallIso_trans, Iso.trans_assoc] using congrArg smallIso hraw

/-- All twenty-five source nodes of the first product retain the full original left chart row. -/
theorem polynomial_product_source_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (i j : Fin 5) :
    polynomialProductNodes P u v w α hc
      (Quillen.SimplexGrid.index 17 4 (CoefficientMovingSquareRows.outerRow i, j)) =
      ModelSimplex.reanchorNodes (h0Anchor P (u ≫ v) w)
        (BassH1References.chartNodes P (u ≫ v) w α hc)
        (Quillen.SimplexGrid.index 4 4 (i, j)) := by
  have h := product_first_reanchor _
    (movingSquareSource P (polynomialUnderCoefficient R) u v)
    (CoefficientSquareFamilies.polynomialSource P (u ≫ v))
    (CoefficientSquareFamilies.chartSource P w α)
    (CoefficientSquareFamilies.polynomialNodes P (u ≫ v))
    (CoefficientSquareFamilies.chartNodes P w α)
    (polynomialDirectAnchor P u v) (polynomialProductAnchor P u v w α hc) i j
  refine Eq.trans ?_ (h.trans ?_)
  · unfold polynomialProductNodes reanchoredProductNode
      CommonReferenceProduct.vertices CommonReferenceProduct.references
    rw [Quillen.SimplexGrid.decode_index 17 4, Quillen.SimplexGrid.decode_index 4 4]
    dsimp only
    rw [polynomial_direct_nodes]
    rfl
  · rw [polynomial_product_source_anchor]
    simp only [reanchoredProductNode, ModelSimplex.reanchorNodes,
      BassH1References.chartNodes, Iso.trans_assoc]
    rfl

/-- All twenty-five source nodes of the second product retain the right chart reference. -/
theorem chart_product_source_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (i j : Fin 5) :
    chartProductNodes P u v w α hd
      (Quillen.SimplexGrid.index 4 17 (i, CoefficientMovingSquareRows.outerRow j)) =
      ModelSimplex.reanchorNodes (rightStartingAnchor P u v w)
        (BassH1References.chartNodes P u (v ≫ w) α hb)
        (Quillen.SimplexGrid.index 4 4 (i, j)) := by
  have h := product_second_reanchor _ (CoefficientSquareFamilies.polynomialSource P u)
    (movingSquareSource P α v w) (CoefficientSquareFamilies.chartSource P (v ≫ w) α)
    (CoefficientSquareFamilies.polynomialNodes P u)
    (CoefficientSquareFamilies.chartNodes P (v ≫ w) α)
    (chartDirectAnchor P v w α) (chartProductAnchor P u v w α hd) i j
  refine Eq.trans ?_ (h.trans ?_)
  · unfold chartProductNodes reanchoredProductNode
      CommonReferenceProduct.vertices CommonReferenceProduct.references
    rw [Quillen.SimplexGrid.decode_index 4 17, Quillen.SimplexGrid.decode_index 4 4]
    dsimp only
    rw [chart_direct_nodes]
    rfl
  · rw [chart_product_source_anchor P u v w α hb hd]
    simp only [reanchoredProductNode, ModelSimplex.reanchorNodes,
      BassH1References.chartNodes, Iso.trans_assoc]

/-- All twenty-five terminal polynomial nodes equal the full prewhiskered original chart. -/
theorem polynomial_product_target_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (i j : Fin 5) :
    polynomialProductNodes P u v w α hc
      (Quillen.SimplexGrid.index 17 4 (CoefficientMovingSquareRows.secondRow i, j)) =
      preReferenceNode _ (coefficientModel P u) (precompAnchor P u v w)
        (BassH1References.chartNodes P v w α hc (Quillen.SimplexGrid.index 4 4 (i, j))) := by
  unfold polynomialProductNodes
  rw [product_node_index, polynomial_second_nodes]
  change CommonReferenceProduct.node _ _ _ _ (CommonReferenceProduct.preNode _ _ _ _) _ = _
  rw [CommonReferenceProduct.pre_node_reanchor,
    CommonReferenceProduct.node_first_reanchor, polynomial_product_target_anchor,
    CommonReferenceProduct.node_precomp]
  unfold preReferenceNode CommonReferenceProduct.preNode CommonReferenceProduct.reanchor
    CommonReferenceNerve.precompNode CommonReferenceProduct.node BassH1References.chartNodes
    CommonReferenceProduct.vertices CommonReferenceProduct.references
  rw [Quillen.SimplexGrid.decode_index]
  simp only [Iso.refl_trans, isoWhiskerLeft_trans, Iso.trans_assoc]

/-- All twenty-five terminal chart nodes equal the full Laurent-postwhiskered original chart. -/
theorem chart_product_target_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (i j : Fin 5) :
    chartProductNodes P u v w α hd
      (Quillen.SimplexGrid.index 4 17 (i, CoefficientMovingSquareRows.firstRow j)) =
      postReferenceNode _ (coefficientModel P ((laurentUnderFunctor R).map w))
        (postcompAnchor P u v w)
        (BassH1References.chartNodes P u v α hb (Quillen.SimplexGrid.index 4 4 (i, j))) := by
  unfold chartProductNodes
  rw [product_node_index, chart_first_nodes]
  change CommonReferenceProduct.node _ _ _ _ _ (CommonReferenceProduct.postNode _ _ _ _) = _
  rw [CommonReferenceProduct.post_node_reanchor,
    CommonReferenceProduct.node_second_reanchor, chart_product_target_anchor P u v w α hb hd,
    CommonReferenceProduct.node_postcomp]
  unfold postReferenceNode CommonReferenceProduct.postNode CommonReferenceProduct.reanchor
    CommonReferenceNerve.postcompNode CommonReferenceProduct.node BassH1References.chartNodes
    CommonReferenceProduct.vertices CommonReferenceProduct.references
  rw [Quillen.SimplexGrid.decode_index]
  simp only [Iso.refl_trans, isoWhiskerRight_trans, Iso.trans_assoc]

/-- The middle seam identifies all twenty-five full nodes, including both canonical references. -/
theorem product_middle_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (i j : Fin 5) :
    polynomialProductNodes P u v w α hc
      (Quillen.SimplexGrid.index 17 4 (CoefficientMovingSquareRows.firstRow i, j)) =
      chartProductNodes P u v w α hd
        (Quillen.SimplexGrid.index 4 17 (i, CoefficientMovingSquareRows.secondRow j)) := by
  unfold polynomialProductNodes chartProductNodes
  rw [product_node_index, product_node_index, polynomial_first_nodes, chart_second_nodes]
  change CommonReferenceProduct.node _ _ _ _ (CommonReferenceProduct.postNode _ _ _ _) _ =
    CommonReferenceProduct.node _ _ _ _ _ (CommonReferenceProduct.preNode _ _ _ _)
  rw [CommonReferenceProduct.post_node_reanchor, CommonReferenceProduct.pre_node_reanchor,
    CommonReferenceProduct.node_first_reanchor, CommonReferenceProduct.node_second_reanchor,
    product_middle_anchor P u v w α hc hd]
  exact CommonReferenceProduct.node_associativity _ _ _ _ _ _ _

/-- The entire first source face uses the exact twenty-five full left chart nodes. -/
theorem polynomial_product_source_parameter
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (s t : unitInterval) :
    polynomialProductPrism P u v w α hc inverse ![0, s, t] =
      CommonReferenceNerve.parameter _ (ModelSimplex.reanchorNodes (h0Anchor P (u ≫ v) w)
        (BassH1References.chartNodes P (u ≫ v) w α hc))
        (Quillen.SimplexGrid.parameter.{u + 1} 4 4
          (NativeSquareFiveSimplex.parameter (productPolynomialTime inverse t),
            NativeSquareFiveSimplex.parameter s)) := by
  change CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w α hc)
    (Quillen.SimplexGrid.parameter.{u + 1} 17 4
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter
        (0, productPolynomialTime inverse t), NativeSquareFiveSimplex.parameter s)) = _
  rw [CoefficientMovingSquareRows.moving_zero_row]
  refine (first_product_parameter _ _ 0 _ _).trans ?_
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter _ N _)
  funext k
  obtain ⟨⟨i, j⟩, rfl⟩ := (Quillen.SimplexGrid.indexEquiv 4 4).surjective k
  rw [← Quillen.SimplexGrid.index_eq_equiv]
  simp only [firstProductRow, Quillen.SimplexGrid.decode_index]
  exact polynomial_product_source_nodes P u v w α hc i j

/-- The entire second source face retains the right cube's specified association reference. -/
theorem chart_product_source_parameter
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (s t : unitInterval) :
    chartProductPrism P u v w α hd inverse ![0, s, t] =
      CommonReferenceNerve.parameter _ (ModelSimplex.reanchorNodes (rightStartingAnchor P u v w)
        (BassH1References.chartNodes P u (v ≫ w) α hb))
        (Quillen.SimplexGrid.parameter.{u + 1} 4 4
          (NativeSquareFiveSimplex.parameter (productPolynomialTime inverse t),
            NativeSquareFiveSimplex.parameter s)) := by
  change CommonReferenceNerve.parameter _ (chartProductNodes P u v w α hd)
    (Quillen.SimplexGrid.parameter.{u + 1} 4 17
      (NativeSquareFiveSimplex.parameter (productPolynomialTime inverse t),
        DoubleSquareScalarPaths.coefficientMovingSquareParameter (0, s))) = _
  rw [CoefficientMovingSquareRows.moving_zero_row]
  refine (second_product_parameter _ _ 0 _ _).trans ?_
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter _ N _)
  funext k
  obtain ⟨⟨i, j⟩, rfl⟩ := (Quillen.SimplexGrid.indexEquiv 4 4).surjective k
  rw [← Quillen.SimplexGrid.index_eq_equiv]
  simp only [secondProductRow, Quillen.SimplexGrid.decode_index]
  exact chart_product_source_nodes P u v w α hb hd i j

/-- The positive first prism starts on the whole original left positive component. -/
theorem polynomial_product_plus_source_face (s t : unitInterval) :
    polynomialProductPrism P u v w (underToLaurent R) (laurentPlus_projection P c)
      false ![0, s, t] =
      cubeLift P (u ≫ v) w (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (h0Anchor P (u ≫ v) w) ![1, upper s, lower t] := by
  rw [polynomial_product_source_parameter]
  change _ = CommonReferenceNerve.parameter _
    (ModelSimplex.reanchorNodes (h0Anchor P (u ≫ v) w) (BassMWhole.nodes P (u ≫ v) w))
    (BassMWhole.scalarCube.{u} ![1, upper s, lower t])
  rw [plus_component_parameter]
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter _ N
    (BassH1Components.plusParameter.{u} (s, t)))
  funext i
  change _ = anchorNode (h0Anchor P (u ≫ v) w)
    (BassMWhole.nodes P (u ≫ v) w (BassMWholeOrder.oldIndex (BassH1Order.plusProductIndex i)))
  rw [BassMWhole.old_nodes, BassH1Merged.plus_nodes]
  rfl

/-- The inverse first prism keeps its reversed polynomial time on the whole old inverse piece. -/
theorem polynomial_product_minus_source_face (s t : unitInterval) :
    polynomialProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P c)
      true ![0, s, t] =
      cubeLift P (u ≫ v) w (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (h0Anchor P (u ≫ v) w) ![1, upper s, upper (upper t)] := by
  rw [polynomial_product_source_parameter]
  change _ = CommonReferenceNerve.parameter _
    (ModelSimplex.reanchorNodes (h0Anchor P (u ≫ v) w) (BassMWhole.nodes P (u ≫ v) w))
    (BassMWhole.scalarCube.{u} ![1, upper s, upper (upper t)])
  rw [minus_component_parameter]
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter _ N
    (BassH1Components.minusParameter.{u} (s, t)))
  funext i
  change _ = anchorNode (h0Anchor P (u ≫ v) w)
    (BassMWhole.nodes P (u ≫ v) w (BassMWholeOrder.oldIndex (BassH1Order.minusProductIndex i)))
  rw [BassMWhole.old_nodes, BassH1Merged.minus_nodes]
  rfl

/-- The positive second prism starts on the whole original right positive component. -/
theorem chart_product_plus_source_face (s t : unitInterval) :
    chartProductPrism P u v w (underToLaurent R) (laurentPlus_projection P d)
      false ![0, s, t] =
      cubeLift P u (v ≫ w) (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (rightStartingAnchor P u v w) ![1, upper s, lower t] := by
  rw [chart_product_source_parameter P u v w _ (laurentPlus_projection P b)]
  change _ = CommonReferenceNerve.parameter _
    (ModelSimplex.reanchorNodes (rightStartingAnchor P u v w) (BassMWhole.nodes P u (v ≫ w)))
    (BassMWhole.scalarCube.{u} ![1, upper s, lower t])
  rw [plus_component_parameter]
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter _ N
    (BassH1Components.plusParameter.{u} (s, t)))
  funext i
  change _ = anchorNode (rightStartingAnchor P u v w)
    (BassMWhole.nodes P u (v ≫ w) (BassMWholeOrder.oldIndex (BassH1Order.plusProductIndex i)))
  rw [BassMWhole.old_nodes, BassH1Merged.plus_nodes]
  rfl

/-- The inverse second prism starts on the unchanged final-quarter right inverse component. -/
theorem chart_product_minus_source_face (s t : unitInterval) :
    chartProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P d)
      true ![0, s, t] =
      cubeLift P u (v ≫ w) (BassH0Diagram.reference P ((u ≫ v) ≫ w))
        (rightStartingAnchor P u v w) ![1, upper s, upper (upper t)] := by
  rw [chart_product_source_parameter P u v w _ (laurentMinus_projection P b)]
  change _ = CommonReferenceNerve.parameter _
    (ModelSimplex.reanchorNodes (rightStartingAnchor P u v w) (BassMWhole.nodes P u (v ≫ w)))
    (BassMWhole.scalarCube.{u} ![1, upper s, upper (upper t)])
  rw [minus_component_parameter]
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter _ N
    (BassH1Components.minusParameter.{u} (s, t)))
  funext i
  change _ = anchorNode (rightStartingAnchor P u v w)
    (BassMWhole.nodes P u (v ≫ w) (BassMWholeOrder.oldIndex (BassH1Order.minusProductIndex i)))
  rw [BassMWhole.old_nodes, BassH1Merged.minus_nodes]
  rfl

private theorem polynomial_target_parameter
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (s t : unitInterval) :
    polynomialProductPrism P u v w α hc false ![1, s, upper t] =
      CommonReferenceNerve.parameter _
        (fun k ↦ preReferenceNode _ (coefficientModel P u) (precompAnchor P u v w)
          (BassH1References.chartNodes P v w α hc k))
        (Quillen.SimplexGrid.parameter.{u + 1} 4 4
          (NativeSquareFiveSimplex.parameter t, NativeSquareFiveSimplex.parameter s)) := by
  change CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w α hc)
    (Quillen.SimplexGrid.parameter.{u + 1} 17 4
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (1, upper t),
        NativeSquareFiveSimplex.parameter s)) = _
  rw [CoefficientMovingSquareRows.moving_one_upper_row]
  refine (first_product_parameter _ _ 2 _ _).trans ?_
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter _ N _)
  funext k
  obtain ⟨⟨i, j⟩, rfl⟩ := (Quillen.SimplexGrid.indexEquiv 4 4).surjective k
  rw [← Quillen.SimplexGrid.index_eq_equiv]
  simp only [firstProductRow, Quillen.SimplexGrid.decode_index]
  exact polynomial_product_target_nodes P u v w α hc i j

private theorem chart_target_parameter
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (s t : unitInterval) :
    chartProductPrism P u v w α hd false ![1, lower s, t] =
      CommonReferenceNerve.parameter _
        (fun k ↦ postReferenceNode _ (coefficientModel P ((laurentUnderFunctor R).map w))
          (postcompAnchor P u v w) (BassH1References.chartNodes P u v α hb k))
        (Quillen.SimplexGrid.parameter.{u + 1} 4 4
          (NativeSquareFiveSimplex.parameter t, NativeSquareFiveSimplex.parameter s)) := by
  change CommonReferenceNerve.parameter _ (chartProductNodes P u v w α hd)
    (Quillen.SimplexGrid.parameter.{u + 1} 4 17
      (NativeSquareFiveSimplex.parameter t,
        DoubleSquareScalarPaths.coefficientMovingSquareParameter (1, lower s))) = _
  rw [CoefficientMovingSquareRows.moving_one_lower_row]
  refine (second_product_parameter _ _ 1 _ _).trans ?_
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter _ N _)
  funext k
  obtain ⟨⟨i, j⟩, rfl⟩ := (Quillen.SimplexGrid.indexEquiv 4 4).surjective k
  rw [← Quillen.SimplexGrid.index_eq_equiv]
  simp only [secondProductRow, Quillen.SimplexGrid.decode_index]
  exact chart_product_target_nodes P u v w α hb hd i j

private theorem product_middle_parameter
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (s t : unitInterval) :
    polynomialProductPrism P u v w α hc false ![1, s, lower t] =
      chartProductPrism P u v w α hd false ![1, upper s, t] := by
  change CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w α hc)
    (Quillen.SimplexGrid.parameter.{u + 1} 17 4
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (1, lower t),
        NativeSquareFiveSimplex.parameter s)) =
      CommonReferenceNerve.parameter _ (chartProductNodes P u v w α hd)
        (Quillen.SimplexGrid.parameter.{u + 1} 4 17
          (NativeSquareFiveSimplex.parameter t,
            DoubleSquareScalarPaths.coefficientMovingSquareParameter (1, upper s)))
  rw [CoefficientMovingSquareRows.moving_one_lower_row,
    CoefficientMovingSquareRows.moving_one_upper_row]
  refine (first_product_parameter _ _ 1 _ _).trans ?_
  refine Eq.trans ?_ (second_product_parameter _ _ 2 _ _).symm
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter _ N _)
  funext k
  obtain ⟨⟨i, j⟩, rfl⟩ := (Quillen.SimplexGrid.indexEquiv 4 4).surjective k
  rw [← Quillen.SimplexGrid.index_eq_equiv]
  simp only [firstProductRow, secondProductRow, Quillen.SimplexGrid.decode_index]
  exact product_middle_nodes P u v w α hc hd i j

private theorem reverse_lower (t : unitInterval) :
    unitInterval.symm (lower t) = upper (unitInterval.symm t) := by
  apply Subtype.ext
  change 1 - (t : ℝ) / 2 = (1 - (t : ℝ) + 1) / 2
  ring

private theorem reverse_upper (t : unitInterval) :
    unitInterval.symm (upper t) = lower (unitInterval.symm t) := by
  apply Subtype.ext
  change 1 - ((t : ℝ) + 1) / 2 = (1 - (t : ℝ)) / 2
  ring

/-- The entire positive upper terminal half is the original source-whiskered positive cube. -/
theorem polynomial_product_plus_target_face (s t : unitInterval) :
    polynomialProductPrism P u v w (underToLaurent R) (laurentPlus_projection P c)
      false ![1, s, upper t] = precompLift P u v w ![1, upper s, lower t] := by
  rw [polynomial_target_parameter]
  change _ = CommonReferenceNerve.parameter _ (precompNodes P u v w)
    (BassMWhole.scalarCube.{u} ![1, upper s, lower t])
  rw [plus_component_parameter]
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter _ N
    (BassH1Components.plusParameter.{u} (s, t)))
  funext i
  change _ = preReferenceNode _ (coefficientModel P u) (precompAnchor P u v w)
    (BassMWhole.nodes P v w (BassMWholeOrder.oldIndex (BassH1Order.plusProductIndex i)))
  rw [BassMWhole.old_nodes, BassH1Merged.plus_nodes]

/-- Inversion swaps the terminal halves while retaining the original inverse cube coordinates. -/
theorem polynomial_product_minus_target_face (s t : unitInterval) :
    polynomialProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P c)
      true ![1, s, lower t] = precompLift P u v w ![1, upper s, upper (upper t)] := by
  change polynomialProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P c)
    false ![1, s, unitInterval.symm (lower t)] = _
  rw [reverse_lower, polynomial_target_parameter]
  change _ = CommonReferenceNerve.parameter _ (precompNodes P u v w)
    (BassMWhole.scalarCube.{u} ![1, upper s, upper (upper t)])
  rw [minus_component_parameter]
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter _ N
    (BassH1Components.minusParameter.{u} (s, t)))
  funext i
  change _ = preReferenceNode _ (coefficientModel P u) (precompAnchor P u v w)
    (BassMWhole.nodes P v w (BassMWholeOrder.oldIndex (BassH1Order.minusProductIndex i)))
  rw [BassMWhole.old_nodes, BassH1Merged.minus_nodes]

/-- The entire first chart terminal half is the original Laurent-postcomposed positive cube. -/
theorem chart_product_plus_target_face (s t : unitInterval) :
    chartProductPrism P u v w (underToLaurent R) (laurentPlus_projection P d)
      false ![1, lower s, t] = postcompLift P u v w ![1, upper s, lower t] := by
  rw [chart_target_parameter P u v w _ (laurentPlus_projection P b)]
  change _ = CommonReferenceNerve.parameter _ (postcompNodes P u v w)
    (BassMWhole.scalarCube.{u} ![1, upper s, lower t])
  rw [plus_component_parameter]
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter _ N
    (BassH1Components.plusParameter.{u} (s, t)))
  funext i
  change _ = postReferenceNode _ (coefficientModel P ((laurentUnderFunctor R).map w))
    (postcompAnchor P u v w)
    (BassMWhole.nodes P u v (BassMWholeOrder.oldIndex (BassH1Order.plusProductIndex i)))
  rw [BassMWhole.old_nodes, BassH1Merged.plus_nodes]

/-- The other chart has the same whole terminal half and the original final-quarter reversal. -/
theorem chart_product_minus_target_face (s t : unitInterval) :
    chartProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P d)
      true ![1, lower s, t] = postcompLift P u v w ![1, upper s, upper (upper t)] := by
  change chartProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P d)
    false ![1, lower s, unitInterval.symm t] = _
  rw [chart_target_parameter P u v w _ (laurentMinus_projection P b)]
  change _ = CommonReferenceNerve.parameter _ (postcompNodes P u v w)
    (BassMWhole.scalarCube.{u} ![1, upper s, upper (upper t)])
  rw [minus_component_parameter]
  apply congrArg (fun N ↦ CommonReferenceNerve.parameter _ N
    (BassH1Components.minusParameter.{u} (s, t)))
  funext i
  change _ = postReferenceNode _ (coefficientModel P ((laurentUnderFunctor R).map w))
    (postcompAnchor P u v w)
    (BassMWhole.nodes P u v (BassMWholeOrder.oldIndex (BassH1Order.minusProductIndex i)))
  rw [BassMWhole.old_nodes, BassH1Merged.minus_nodes]

/-- The entire positive middle seam identifies the two actual full-reference product prisms. -/
theorem product_plus_middle_face (s t : unitInterval) :
    polynomialProductPrism P u v w (underToLaurent R) (laurentPlus_projection P c)
      false ![1, s, lower t] =
      chartProductPrism P u v w (underToLaurent R) (laurentPlus_projection P d)
        false ![1, upper s, t] :=
  product_middle_parameter P u v w _ _ _ s t

/-- The entire inverse middle seam retains its exact lower/upper swap and unchanged chart time. -/
theorem product_minus_middle_face (s t : unitInterval) :
    polynomialProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P c)
      true ![1, s, upper t] =
      chartProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P d)
        true ![1, upper s, t] := by
  change polynomialProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P c)
    false ![1, s, unitInterval.symm (upper t)] =
      chartProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P d)
        false ![1, upper s, unitInterval.symm t]
  rw [reverse_upper]
  exact product_middle_parameter P u v w _ _ _ s (unitInterval.symm t)

end Quillen.PerfectComplexes.BassMWholeNerve
