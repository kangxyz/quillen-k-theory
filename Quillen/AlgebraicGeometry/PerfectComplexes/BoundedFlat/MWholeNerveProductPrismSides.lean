/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Naturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveCompositionPrismEndpoints
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveProductPrismEndpoints
public import Quillen.Topology.Realization.SimplexGridProductFaces
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ProjectionRectangleSquareRows

/-!
# Full sides and canonical seams of the original product prisms

The sixteen raw sides retain the actual ninety-node product and its specified anchors.
The coefficient and Laurent seams identify all fifteen full dependent nodes through an
accepted source corner and reference-isomorphism cancellation. Their whole characteristic
maps are compared only on the original eight primitive product supports; inverse polynomial
and independent structure coordinates are not changed. No whole relative boundary or filler
is constructed here.
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

/-- The two actual ordered moving sides. The side selector is not a time coordinate. -/
def productSideRow (e : Fin 2) : Fin 3 → Fin 18 :=
  ![CoefficientMovingSquareRows.sourceSide, CoefficientMovingSquareRows.targetSide] e

/-- Embed the selected moving row in the ordered polynomial product grid. -/
def polynomialSideIndex (e : Fin 2) (k : Fin 15) : Fin 90 :=
  Quillen.SimplexGrid.index 17 4
    (productSideRow e ((Quillen.SimplexGrid.indexEquiv 2 4).symm k).1,
      ((Quillen.SimplexGrid.indexEquiv 2 4).symm k).2)

/-- Embed the selected moving row in the ordered chart product grid. -/
def chartSideIndex (e : Fin 2) (k : Fin 15) : Fin 90 :=
  Quillen.SimplexGrid.index 4 17
    (((Quillen.SimplexGrid.indexEquiv 4 2).symm k).1,
      productSideRow e ((Quillen.SimplexGrid.indexEquiv 4 2).symm k).2)

/-- Only these ordered side embeddings, never the whole moving square, are used. -/
theorem polynomialSideIndex_monotone (e : Fin 2) : Monotone (polynomialSideIndex e) :=
  (by decide : ∀ e : Fin 2, Monotone (polynomialSideIndex e)) e

theorem chartSideIndex_monotone (e : Fin 2) : Monotone (chartSideIndex e) :=
  (by decide : ∀ e : Fin 2, Monotone (chartSideIndex e)) e

theorem polynomial_side_index (e : Fin 2) (i : Fin 3) (j : Fin 5) :
    polynomialSideIndex e (Quillen.SimplexGrid.index 2 4 (i, j)) =
      Quillen.SimplexGrid.index 17 4 (productSideRow e i, j) := by
  unfold polynomialSideIndex
  rw [Quillen.SimplexGrid.decode_index]

theorem chart_side_index (e : Fin 2) (i : Fin 5) (j : Fin 3) :
    chartSideIndex e (Quillen.SimplexGrid.index 4 2 (i, j)) =
      Quillen.SimplexGrid.index 4 17 (i, productSideRow e j) := by
  unfold chartSideIndex
  rw [Quillen.SimplexGrid.decode_index]

/-- Whole fifteen-node characteristic restriction, including every dependent reference. -/
theorem polynomial_side_parameter {V W : Model.{u}} (F : V ⟶ W)
    (N : Fin 90 → CommonReferenceNerve.Node F) (e : Fin 2)
    (z : StdSimplex ℝ (Fin 3)) (y : StdSimplex ℝ (Fin 5)) :
    CommonReferenceNerve.parameter F N
      (Quillen.SimplexGrid.parameter.{u} 17 4 (StdSimplex.map (productSideRow e) z, y)) =
    CommonReferenceNerve.parameter F (fun i ↦ N (polynomialSideIndex e i))
      (Quillen.SimplexGrid.parameter.{u} 2 4 (z, y)) := by
  let α : ⦋2⦌ ⟶ ⦋17⦌ := SimplexCategory.Hom.mk
    ⟨productSideRow e, CoefficientMovingSquareRows.side_rows_monotone e⟩
  let γ : ⦋14⦌ ⟶ ⦋89⦌ := SimplexCategory.Hom.mk
    ⟨polynomialSideIndex e, polynomialSideIndex_monotone e⟩
  have h := Quillen.SimplexGrid.parameter_productMap.{u} α (𝟙 ⦋4⦌) γ
    (polynomial_side_index e) z y
  have h' : Quillen.SimplexGrid.parameter.{u} 17 4
      (StdSimplex.map (productSideRow e) z, y) =
      StdSimplex.map (polynomialSideIndex e) (Quillen.SimplexGrid.parameter.{u} 2 4 (z, y)) := by
    have hid : StdSimplex.map
        (SimplexCategory.Hom.toOrderHom (𝟙 ⦋4⦌) : Fin 5 → Fin 5) y = y := by
      change StdSimplex.map id y = y
      exact StdSimplex.map_id y
    exact (congrArg (fun t : StdSimplex ℝ (Fin 5) ↦
      Quillen.SimplexGrid.parameter.{u} 17 4 (StdSimplex.map (productSideRow e) z, t))
      hid.symm).trans h
  exact (congrArg (CommonReferenceNerve.parameter F N) h').trans
    (CommonReferenceNerve.parameter_face F N γ _)

/-- The other fifteen-node restriction keeps the original product order. -/
theorem chart_side_parameter {V W : Model.{u}} (F : V ⟶ W)
    (N : Fin 90 → CommonReferenceNerve.Node F) (e : Fin 2)
    (z : StdSimplex ℝ (Fin 5)) (y : StdSimplex ℝ (Fin 3)) :
    CommonReferenceNerve.parameter F N
      (Quillen.SimplexGrid.parameter.{u} 4 17 (z, StdSimplex.map (productSideRow e) y)) =
    CommonReferenceNerve.parameter F (fun i ↦ N (chartSideIndex e i))
      (Quillen.SimplexGrid.parameter.{u} 4 2 (z, y)) := by
  let β : ⦋2⦌ ⟶ ⦋17⦌ := SimplexCategory.Hom.mk
    ⟨productSideRow e, CoefficientMovingSquareRows.side_rows_monotone e⟩
  let γ : ⦋14⦌ ⟶ ⦋89⦌ := SimplexCategory.Hom.mk
    ⟨chartSideIndex e, chartSideIndex_monotone e⟩
  have h := Quillen.SimplexGrid.parameter_productMap.{u} (𝟙 ⦋4⦌) β γ
    (chart_side_index e) z y
  have h' : Quillen.SimplexGrid.parameter.{u} 4 17
      (z, StdSimplex.map (productSideRow e) y) =
      StdSimplex.map (chartSideIndex e) (Quillen.SimplexGrid.parameter.{u} 4 2 (z, y)) := by
    have hid : StdSimplex.map
        (SimplexCategory.Hom.toOrderHom (𝟙 ⦋4⦌) : Fin 5 → Fin 5) z = z := by
      change StdSimplex.map id z = z
      exact StdSimplex.map_id z
    exact (congrArg (fun t : StdSimplex ℝ (Fin 5) ↦
      Quillen.SimplexGrid.parameter.{u} 4 17 (t, StdSimplex.map (productSideRow e) y))
      hid.symm).trans h
  exact (congrArg (CommonReferenceNerve.parameter F N) h').trans
    (CommonReferenceNerve.parameter_face F N γ _)


/-- A full product node cancels its actual anchor; equality of functors alone is not used. -/
private theorem product_anchor_eq {V W T : Model.{u}}
    (F : V ⟶ T) (H : V ⟶ W) (G : W ⟶ T)
    (η θ : F.functor ≅ (H ≫ G).functor)
    (N : CommonReferenceNerve.Node H) (M : CommonReferenceNerve.Node G)
    (h : CommonReferenceProduct.node F H G η N M =
      CommonReferenceProduct.node F H G θ N M) : η = θ := by
  have hs := eq_of_heq (Sigma.mk.inj h).2
  change η ≪≫ _ = θ ≪≫ _ at hs
  have hc := congrArg (fun ν ↦ ν ≪≫
    ((Functor.uncurry.obj (whiskeringLeft _ _ _)).mapIso (N.2.prod M.2)).symm) hs
  simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using hc

/-- Two whole product families are associated using their actual references and one full corner.
This theorem does not assume or manufacture a canonical corner equality. -/
private theorem product_association_of_corner
    {V W W' T : Model.{u}} {Ix K : Type}
    (F : V ⟶ T) (H : V ⟶ W) (J : W ⟶ W') (G : W' ⟶ T)
    (L : V ⟶ W') (R : W ⟶ T)
    (τ : L.functor ≅ (H ≫ J).functor) (ρ : R.functor ≅ (J ≫ G).functor)
    (η : F.functor ≅ (L ≫ G).functor) (θ : F.functor ≅ (H ≫ R).functor)
    (N : Ix → CommonReferenceNerve.Node H) (M : K → CommonReferenceNerve.Node G)
    (i₀ : Ix) (j₀ : K)
    (h : CommonReferenceProduct.node F L G η
        (CommonReferenceProduct.postNode L J τ (N i₀)) (M j₀) =
      CommonReferenceProduct.node F H R θ (N i₀)
        (CommonReferenceProduct.preNode R J ρ (M j₀))) (i : Ix) (j : K) :
    CommonReferenceProduct.node F L G η
        (CommonReferenceProduct.postNode L J τ (N i)) (M j) =
      CommonReferenceProduct.node F H R θ (N i)
        (CommonReferenceProduct.preNode R J ρ (M j)) := by
  rw [CommonReferenceProduct.post_node_reanchor,
    CommonReferenceProduct.pre_node_reanchor,
    CommonReferenceProduct.node_first_reanchor,
    CommonReferenceProduct.node_second_reanchor,
    CommonReferenceProduct.node_associativity] at h ⊢
  have he := product_anchor_eq F H (J ≫ G) _ _ (N i₀)
    (CommonReferenceProduct.preNode (J ≫ G) J (Iso.refl _) (M j₀)) h
  rw [he]

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)

/-- Whole original plus polynomial side; the ninety full nodes retain their raw anchor. -/
theorem polynomial_product_plus_s0_raw (q y : unitInterval) :
    polynomialProductPrism P u v w (underToLaurent R) (laurentPlus_projection P c) false ![q, 0,
      y] =
    CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w (underToLaurent R)
      (laurentPlus_projection P c))
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, y), StdSimplex.single 2)) :=
          by
  change CommonReferenceNerve.parameter _
    (polynomialProductNodes P u v w (underToLaurent R) (laurentPlus_projection P c))
    (Quillen.SimplexGrid.parameter.{u + 1} 17 4
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, y),
        NativeSquareFiveSimplex.parameter 0)) = _
  simp only [Path.source]

/-- Whole original plus polynomial side; the ninety full nodes retain their raw anchor. -/
theorem polynomial_product_plus_s1_raw (q y : unitInterval) :
    polynomialProductPrism P u v w (underToLaurent R) (laurentPlus_projection P c) false ![q, 1,
      y] =
    CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w (underToLaurent R)
      (laurentPlus_projection P c))
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, y), StdSimplex.single 4)) :=
          by
  change CommonReferenceNerve.parameter _
    (polynomialProductNodes P u v w (underToLaurent R) (laurentPlus_projection P c))
    (Quillen.SimplexGrid.parameter.{u + 1} 17 4
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, y),
        NativeSquareFiveSimplex.parameter 1)) = _
  simp only [Path.target]

/-- Whole original plus polynomial side; the ninety full nodes retain their raw anchor. -/
theorem polynomial_product_plus_t0_raw (q y : unitInterval) :
    polynomialProductPrism P u v w (underToLaurent R) (laurentPlus_projection P c) false ![q, y,
      0] =
    CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w (underToLaurent R)
      (laurentPlus_projection P c))
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (StdSimplex.map CoefficientMovingSquareRows.targetSide (binaryPath (k := 2) 0 1 2 q),
          NativeSquareFiveSimplex.parameter y)) := by
  change CommonReferenceNerve.parameter _
    (polynomialProductNodes P u v w (underToLaurent R) (laurentPlus_projection P c))
    (Quillen.SimplexGrid.parameter.{u + 1} 17 4
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, 0),
        NativeSquareFiveSimplex.parameter y)) = _
  simp only [CoefficientMovingSquareRows.moving_left_row]

/-- Whole original plus polynomial side; the ninety full nodes retain their raw anchor. -/
theorem polynomial_product_plus_t1_raw (q y : unitInterval) :
    polynomialProductPrism P u v w (underToLaurent R) (laurentPlus_projection P c) false ![q, y,
      1] =
    CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w (underToLaurent R)
      (laurentPlus_projection P c))
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (StdSimplex.map CoefficientMovingSquareRows.sourceSide (binaryPath (k := 2) 0 1 2 q),
          NativeSquareFiveSimplex.parameter y)) := by
  change CommonReferenceNerve.parameter _
    (polynomialProductNodes P u v w (underToLaurent R) (laurentPlus_projection P c))
    (Quillen.SimplexGrid.parameter.{u + 1} 17 4
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, 1),
        NativeSquareFiveSimplex.parameter y)) = _
  simp only [CoefficientMovingSquareRows.moving_right_row]

/-- Whole original minus polynomial side; the ninety full nodes retain their raw anchor. -/
theorem polynomial_product_minus_s0_raw (q y : unitInterval) :
    polynomialProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P c) true
      ![q, 0, y] =
    CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w (underToLaurentInvert R)
      (laurentMinus_projection P c))
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, unitInterval.symm y),
          StdSimplex.single 2)) := by
  change CommonReferenceNerve.parameter _
    (polynomialProductNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P c))
    (Quillen.SimplexGrid.parameter.{u + 1} 17 4
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, unitInterval.symm y),
        NativeSquareFiveSimplex.parameter 0)) = _
  simp only [Path.source]

/-- Whole original minus polynomial side; the ninety full nodes retain their raw anchor. -/
theorem polynomial_product_minus_s1_raw (q y : unitInterval) :
    polynomialProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P c) true
      ![q, 1, y] =
    CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w (underToLaurentInvert R)
      (laurentMinus_projection P c))
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, unitInterval.symm y),
          StdSimplex.single 4)) := by
  change CommonReferenceNerve.parameter _
    (polynomialProductNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P c))
    (Quillen.SimplexGrid.parameter.{u + 1} 17 4
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, unitInterval.symm y),
        NativeSquareFiveSimplex.parameter 1)) = _
  simp only [Path.target]

/-- Whole original minus polynomial side; the ninety full nodes retain their raw anchor. -/
theorem polynomial_product_minus_t0_raw (q y : unitInterval) :
    polynomialProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P c) true
      ![q, y, 0] =
    CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w (underToLaurentInvert R)
      (laurentMinus_projection P c))
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (StdSimplex.map CoefficientMovingSquareRows.sourceSide (binaryPath (k := 2) 0 1 2 q),
          NativeSquareFiveSimplex.parameter y)) := by
  change CommonReferenceNerve.parameter _
    (polynomialProductNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P c))
    (Quillen.SimplexGrid.parameter.{u + 1} 17 4
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, unitInterval.symm 0),
        NativeSquareFiveSimplex.parameter y)) = _
  simp only [unitInterval.symm_zero, CoefficientMovingSquareRows.moving_right_row]

/-- Whole original minus polynomial side; the ninety full nodes retain their raw anchor. -/
theorem polynomial_product_minus_t1_raw (q y : unitInterval) :
    polynomialProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P c) true
      ![q, y, 1] =
    CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w (underToLaurentInvert R)
      (laurentMinus_projection P c))
      (Quillen.SimplexGrid.parameter.{u + 1} 17 4
        (StdSimplex.map CoefficientMovingSquareRows.targetSide (binaryPath (k := 2) 0 1 2 q),
          NativeSquareFiveSimplex.parameter y)) := by
  change CommonReferenceNerve.parameter _
    (polynomialProductNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P c))
    (Quillen.SimplexGrid.parameter.{u + 1} 17 4
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, unitInterval.symm 1),
        NativeSquareFiveSimplex.parameter y)) = _
  simp only [unitInterval.symm_one, CoefficientMovingSquareRows.moving_left_row]

/-- Whole original plus chart side; the ninety full nodes retain their raw anchor. -/
theorem chart_product_plus_s0_raw (q y : unitInterval) :
    chartProductPrism P u v w (underToLaurent R) (laurentPlus_projection P d) false ![q, 0, y] =
    CommonReferenceNerve.parameter _ (chartProductNodes P u v w (underToLaurent R)
      (laurentPlus_projection P d))
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (NativeSquareFiveSimplex.parameter (y), StdSimplex.map
          CoefficientMovingSquareRows.targetSide (binaryPath (k := 2) 0 1 2 q))) := by
  change CommonReferenceNerve.parameter _
    (chartProductNodes P u v w (underToLaurent R) (laurentPlus_projection P d))
    (Quillen.SimplexGrid.parameter.{u + 1} 4 17
      (NativeSquareFiveSimplex.parameter (y),
        DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, 0))) = _
  simp only [CoefficientMovingSquareRows.moving_left_row]

/-- Whole original plus chart side; the ninety full nodes retain their raw anchor. -/
theorem chart_product_plus_s1_raw (q y : unitInterval) :
    chartProductPrism P u v w (underToLaurent R) (laurentPlus_projection P d) false ![q, 1, y] =
    CommonReferenceNerve.parameter _ (chartProductNodes P u v w (underToLaurent R)
      (laurentPlus_projection P d))
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (NativeSquareFiveSimplex.parameter (y), StdSimplex.map
          CoefficientMovingSquareRows.sourceSide (binaryPath (k := 2) 0 1 2 q))) := by
  change CommonReferenceNerve.parameter _
    (chartProductNodes P u v w (underToLaurent R) (laurentPlus_projection P d))
    (Quillen.SimplexGrid.parameter.{u + 1} 4 17
      (NativeSquareFiveSimplex.parameter (y),
        DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, 1))) = _
  simp only [CoefficientMovingSquareRows.moving_right_row]

/-- Whole original plus chart side; the ninety full nodes retain their raw anchor. -/
theorem chart_product_plus_t0_raw (q y : unitInterval) :
    chartProductPrism P u v w (underToLaurent R) (laurentPlus_projection P d) false ![q, y, 0] =
    CommonReferenceNerve.parameter _ (chartProductNodes P u v w (underToLaurent R)
      (laurentPlus_projection P d))
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (StdSimplex.single 2, DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, y))) :=
          by
  change CommonReferenceNerve.parameter _
    (chartProductNodes P u v w (underToLaurent R) (laurentPlus_projection P d))
    (Quillen.SimplexGrid.parameter.{u + 1} 4 17
      (NativeSquareFiveSimplex.parameter (0),
        DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, y))) = _
  simp only [Path.source]

/-- Whole original plus chart side; the ninety full nodes retain their raw anchor. -/
theorem chart_product_plus_t1_raw (q y : unitInterval) :
    chartProductPrism P u v w (underToLaurent R) (laurentPlus_projection P d) false ![q, y, 1] =
    CommonReferenceNerve.parameter _ (chartProductNodes P u v w (underToLaurent R)
      (laurentPlus_projection P d))
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (StdSimplex.single 4, DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, y))) :=
          by
  change CommonReferenceNerve.parameter _
    (chartProductNodes P u v w (underToLaurent R) (laurentPlus_projection P d))
    (Quillen.SimplexGrid.parameter.{u + 1} 4 17
      (NativeSquareFiveSimplex.parameter (1),
        DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, y))) = _
  simp only [Path.target]

/-- Whole original minus chart side; the ninety full nodes retain their raw anchor. -/
theorem chart_product_minus_s0_raw (q y : unitInterval) :
    chartProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P d) true ![q, 0,
      y] =
    CommonReferenceNerve.parameter _ (chartProductNodes P u v w (underToLaurentInvert R)
      (laurentMinus_projection P d))
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (NativeSquareFiveSimplex.parameter (unitInterval.symm y), StdSimplex.map
          CoefficientMovingSquareRows.targetSide (binaryPath (k := 2) 0 1 2 q))) := by
  change CommonReferenceNerve.parameter _
    (chartProductNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P d))
    (Quillen.SimplexGrid.parameter.{u + 1} 4 17
      (NativeSquareFiveSimplex.parameter (unitInterval.symm y),
        DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, 0))) = _
  simp only [CoefficientMovingSquareRows.moving_left_row]

/-- Whole original minus chart side; the ninety full nodes retain their raw anchor. -/
theorem chart_product_minus_s1_raw (q y : unitInterval) :
    chartProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P d) true ![q, 1,
      y] =
    CommonReferenceNerve.parameter _ (chartProductNodes P u v w (underToLaurentInvert R)
      (laurentMinus_projection P d))
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (NativeSquareFiveSimplex.parameter (unitInterval.symm y), StdSimplex.map
          CoefficientMovingSquareRows.sourceSide (binaryPath (k := 2) 0 1 2 q))) := by
  change CommonReferenceNerve.parameter _
    (chartProductNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P d))
    (Quillen.SimplexGrid.parameter.{u + 1} 4 17
      (NativeSquareFiveSimplex.parameter (unitInterval.symm y),
        DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, 1))) = _
  simp only [CoefficientMovingSquareRows.moving_right_row]

/-- Whole original minus chart side; the ninety full nodes retain their raw anchor. -/
theorem chart_product_minus_t0_raw (q y : unitInterval) :
    chartProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P d) true ![q, y,
      0] =
    CommonReferenceNerve.parameter _ (chartProductNodes P u v w (underToLaurentInvert R)
      (laurentMinus_projection P d))
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (StdSimplex.single 4, DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, y))) :=
          by
  change CommonReferenceNerve.parameter _
    (chartProductNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P d))
    (Quillen.SimplexGrid.parameter.{u + 1} 4 17
      (NativeSquareFiveSimplex.parameter (unitInterval.symm 0),
        DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, y))) = _
  simp only [unitInterval.symm_zero, Path.target]

/-- Whole original minus chart side; the ninety full nodes retain their raw anchor. -/
theorem chart_product_minus_t1_raw (q y : unitInterval) :
    chartProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P d) true ![q, y,
      1] =
    CommonReferenceNerve.parameter _ (chartProductNodes P u v w (underToLaurentInvert R)
      (laurentMinus_projection P d))
      (Quillen.SimplexGrid.parameter.{u + 1} 4 17
        (StdSimplex.single 2, DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, y))) :=
          by
  change CommonReferenceNerve.parameter _
    (chartProductNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P d))
    (Quillen.SimplexGrid.parameter.{u + 1} 4 17
      (NativeSquareFiveSimplex.parameter (unitInterval.symm 1),
        DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, y))) = _
  simp only [unitInterval.symm_one, Path.source]

/-- Exact coefficient-prism side indexing; the whole chart word is not declared monotone. -/
def coefficientChartSideIndex (φ : ⦋17⦌ ⟶ ⦋30⦌) (k : Fin 15) : Fin 93 :=
  Quillen.SimplexGrid.index 2 30
    (((Quillen.SimplexGrid.indexEquiv 2 4).symm k).1,
      φ.toOrderHom (ProjectionRectangleSquareRows.chartRow
        ((Quillen.SimplexGrid.indexEquiv 2 4).symm k).2))

/-- The Laurent side retains the actual nonmonotone polynomial word. -/
def laurentPolynomialSideIndex (φ : ⦋17⦌ ⟶ ⦋30⦌) (k : Fin 15) : Fin 93 :=
  Quillen.SimplexGrid.index 30 2
    (φ.toOrderHom (ProjectionRectangleSquareRows.polynomialRow
      ((Quillen.SimplexGrid.indexEquiv 4 2).symm k).1),
      ((Quillen.SimplexGrid.indexEquiv 4 2).symm k).2)

/-- The coefficient-side corner is already fixed by accepted full source faces and H1 joins. -/
theorem coefficient_product_side_corner
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (φ : ⦋17⦌ ⟶ ⦋30⦌)
    (hφ : ∀ i, BassH0Diagram.nodes P w (φ.toOrderHom i) =
      BassH0Diagram.chartNodes P w α hc i) :
    polynomialProductNodes P u v w α hc (Quillen.SimplexGrid.index 17 4 (2, 0)) =
      coefficientPrismNodes P u v w
        (Quillen.SimplexGrid.index 2 30 (0, φ.toOrderHom 9)) := by
  have hl := polynomial_product_source_nodes P u v w α hc 4 0
  have hr := coefficient_prism_source_nodes P u v w (φ.toOrderHom 9)
  refine hl.trans (Eq.trans ?_ hr.symm)
  change anchorNode (h0Anchor P (u ≫ v) w)
    (BassH1References.chartNodes P (u ≫ v) w α hc 20) =
    anchorNode (h0Anchor P (u ≫ v) w)
      (BassMWhole.nodes P (u ≫ v) w (middleIndex (φ.toOrderHom 9)))
  rw [middle_nodes]
  apply congrArg (anchorNode (h0Anchor P (u ≫ v) w))
  change _ = preReferenceNode _ _ (BassH1References.middleIso P (u ≫ v) w)
    (BassH0Diagram.nodes P w (φ.toOrderHom 9))
  rw [hφ]
  exact (BassH1Join.middle_product_chart_nodes P (u ≫ v) w α hc 0).symm

/-- The Laurent-side corner keeps the distinct original right association transport. -/
theorem laurent_product_side_corner
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (φ : ⦋17⦌ ⟶ ⦋30⦌)
    (hφ : ∀ i, BassH0Diagram.nodes P u (φ.toOrderHom i) =
      BassH0Diagram.chartNodes P u α ha i) :
    chartProductNodes P u v w α hd (Quillen.SimplexGrid.index 4 17 (0, 15)) =
      laurentPrismNodes P u v w
        (Quillen.SimplexGrid.index 30 2 (φ.toOrderHom 5, 0)) := by
  have hl := chart_product_source_nodes P u v w α hb hd 0 2
  have hr := laurent_prism_source_nodes P u v w (φ.toOrderHom 5)
  refine hl.trans (Eq.trans ?_ hr.symm)
  change anchorNode (rightStartingAnchor P u v w)
    (BassH1References.chartNodes P u (v ≫ w) α hb 2) =
    anchorNode (rightStartingAnchor P u v w)
      (BassMWhole.nodes P u (v ≫ w) (firstIndex (φ.toOrderHom 5)))
  rw [first_nodes]
  apply congrArg (anchorNode (rightStartingAnchor P u v w))
  change _ = postReferenceNode _ _ (BassH1References.firstIso P u (v ≫ w))
    (BassH0Diagram.nodes P u (φ.toOrderHom 5))
  rw [hφ]
  exact (BassH1Join.first_product_polynomial_nodes P u (v ≫ w) α ha hb 0).symm



private theorem side_product_node_index {V W T : Model.{u}} {p q : ℕ}
    (F : V ⟶ T) (H : V ⟶ W) (G : W ⟶ T)
    (N : Fin (p + 1) → CommonReferenceNerve.Node H)
    (M : Fin (q + 1) → CommonReferenceNerve.Node G)
    (η : F.functor ≅ (H ≫ G).functor) (i : Fin (p + 1)) (j : Fin (q + 1)) :
    reanchoredProductNode F H (fun k ↦ (N k).1) (fun k ↦ (N k).2)
      G (fun k ↦ (M k).1) (fun k ↦ (M k).2) η
      (Quillen.SimplexGrid.index p q (i, j)) =
        CommonReferenceProduct.node F H G η (N i) (M j) := by
  unfold reanchoredProductNode CommonReferenceProduct.vertices CommonReferenceProduct.references
  rw [Quillen.SimplexGrid.decode_index]
  rfl

/-- Full coefficient Pc seam: all fifteen original dependent nodes, not just native values. -/
theorem polynomial_coefficient_side_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (φ : ⦋17⦌ ⟶ ⦋30⦌)
    (hφ : ∀ i, BassH0Diagram.nodes P w (φ.toOrderHom i) =
      BassH0Diagram.chartNodes P w α hc i)
    (i : Fin 3) (j : Fin 5) :
    polynomialProductNodes P u v w α hc
      (Quillen.SimplexGrid.index 17 4 (CoefficientMovingSquareRows.sourceSide i, j)) =
    coefficientPrismNodes P u v w
      (Quillen.SimplexGrid.index 2 30
        (i, φ.toOrderHom (ProjectionRectangleSquareRows.chartRow j))) := by
  have hL (k : Fin 3) : movingSquareNodes P (polynomialUnderCoefficient R) u v
      (CoefficientMovingSquareRows.sourceSide k) = _ :=
    CoefficientMovingSquareRows.source_side_nodes
    (coefficientMap P u) (coefficientMap P v)
    (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (polynomialProjection P a) (polynomialProjection P b) (polynomialProjection P c)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (polynomialUnderCoefficient R) u).symm
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (polynomialUnderCoefficient R) v).symm k
  have hR (k : Fin 5) := ProjectionRectangleSquareRows.chart_row_nodes
    (polynomialProjection P c) (coefficientMap P (α.app c))
    (polynomialProjection P d) (coefficientMap P (α.app d))
    (coefficientMap P w) (coefficientMap P ((polynomialUnderFunctor R).map w))
    (coefficientMap P ((laurentUnderFunctor R).map w))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (polynomialUnderCoefficient R) w)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α w)
      (laurentProjection P c) hc k
  have hR' (k : Fin 5) : BassH0Diagram.nodes P w
      (φ.toOrderHom (ProjectionRectangleSquareRows.chartRow k)) = _ :=
    (hφ _).trans (hR k)
  have h0 := coefficient_product_side_corner P u v w α hc φ hφ
  change polynomialProductNodes P u v w α hc
      (Quillen.SimplexGrid.index 17 4 (CoefficientMovingSquareRows.sourceSide 0, 0)) =
    coefficientPrismNodes P u v w
      (Quillen.SimplexGrid.index 2 30
        (0, φ.toOrderHom (ProjectionRectangleSquareRows.chartRow 0))) at h0
  unfold polynomialProductNodes coefficientPrismNodes at h0 ⊢
  rw [side_product_node_index, side_product_node_index, hL 0, hR' 0] at h0
  rw [side_product_node_index, side_product_node_index, hL i, hR' j]
  exact product_association_of_corner _ _ _ _ _ _ _ _ _ _ _ _ 0 0 h0 i j

/-- Full Laurent Pl seam, keeping the polynomial word and all original target references. -/
theorem chart_laurent_side_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (φ : ⦋17⦌ ⟶ ⦋30⦌)
    (hφ : ∀ i, BassH0Diagram.nodes P u (φ.toOrderHom i) =
      BassH0Diagram.chartNodes P u α ha i)
    (i : Fin 5) (j : Fin 3) :
    laurentPrismNodes P u v w (Quillen.SimplexGrid.index 30 2
      (φ.toOrderHom (ProjectionRectangleSquareRows.polynomialRow i), j)) =
    chartProductNodes P u v w α hd (Quillen.SimplexGrid.index 4 17
      (i, CoefficientMovingSquareRows.targetSide j)) := by
  have hL (k : Fin 5) := ProjectionRectangleSquareRows.polynomial_row_nodes
    (polynomialProjection P a) (coefficientMap P (α.app a))
    (polynomialProjection P b) (coefficientMap P (α.app b))
    (coefficientMap P u) (coefficientMap P ((polynomialUnderFunctor R).map u))
    (coefficientMap P ((laurentUnderFunctor R).map u))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
      (polynomialUnderCoefficient R) u)
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α u)
      (laurentProjection P a) ha k
  have hL' (k : Fin 5) : BassH0Diagram.nodes P u
      (φ.toOrderHom (ProjectionRectangleSquareRows.polynomialRow k)) = _ :=
    (hφ _).trans (hL k)
  have hR (k : Fin 3) : movingSquareNodes P α v w
      (CoefficientMovingSquareRows.targetSide k) = _ :=
    CoefficientMovingSquareRows.target_side_nodes
    (coefficientMap P ((polynomialUnderFunctor R).map v))
    (coefficientMap P ((polynomialUnderFunctor R).map w))
    (coefficientMap P ((laurentUnderFunctor R).map v))
    (coefficientMap P ((laurentUnderFunctor R).map w))
    (coefficientMap P (α.app b)) (coefficientMap P (α.app c)) (coefficientMap P (α.app d))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v).symm
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α w).symm k
  have h0 := (laurent_product_side_corner P u v w α ha hb hd φ hφ).symm
  change laurentPrismNodes P u v w (Quillen.SimplexGrid.index 30 2
      (φ.toOrderHom (ProjectionRectangleSquareRows.polynomialRow 0), 0)) =
    chartProductNodes P u v w α hd (Quillen.SimplexGrid.index 4 17
      (0, CoefficientMovingSquareRows.targetSide 0)) at h0
  unfold laurentPrismNodes chartProductNodes at h0 ⊢
  rw [side_product_node_index, side_product_node_index, hL' 0, hR 0] at h0
  rw [side_product_node_index, side_product_node_index, hL' i, hR j]
  exact product_association_of_corner _ _ _ _ _ _ _ _ _ _ _ _ 0 0 h0 i j



/-- Actual inverse/positive H0 face; this is only a selector, not a new path. -/
def productProjectionFace (inverse : Bool) : ⦋17⦌ ⟶ ⦋30⦌ :=
  if inverse then BassH0Diagram.minusFace else BassH0Diagram.plusFace

/-- The transposed binary/square primitive support retains the original grid order. -/
def chartSideEdgeIndex (i : Fin 4) (j : Fin 2) : Fin 4 → Fin 15 :=
  ![Quillen.SimplexGrid.index 4 2
      (BassH1Support.edgeStart i, BassMPrimitiveSupport.coefficientEdgeStart j),
    Quillen.SimplexGrid.index 4 2
      (BassH1Support.edgeStart i, BassMPrimitiveSupport.coefficientEdgeEnd j),
    Quillen.SimplexGrid.index 4 2
      (BassH1Support.edgeEnd i, BassMPrimitiveSupport.coefficientEdgeStart j),
    Quillen.SimplexGrid.index 4 2
      (BassH1Support.edgeEnd i, BassMPrimitiveSupport.coefficientEdgeEnd j)]

/-- The four-vertex face spanned by the selected chart and coefficient edges. -/
def chartSideEdgeFace (i : Fin 4) (j : Fin 2) : ⦋3⦌ ⟶ ⦋14⦌ :=
  SimplexCategory.Hom.mk ⟨chartSideEdgeIndex i j,
    (by decide : ∀ i : Fin 4, ∀ j : Fin 2, Monotone (chartSideEdgeIndex i j)) i j⟩

/-- Each of the actual eight Pc primitive supports preserves order in the canonical 93 nodes. -/
theorem coefficient_side_primitive_monotone (inverse : Bool) (i : Fin 2) (j : Fin 4) :
    Monotone (coefficientChartSideIndex (productProjectionFace inverse) ∘
      (BassMPrimitiveSupport.middleEdgePairFace i j).toOrderHom) :=
  (by decide : ∀ inverse : Bool, ∀ i : Fin 2, ∀ j : Fin 4,
    Monotone (coefficientChartSideIndex (productProjectionFace inverse) ∘
      (BassMPrimitiveSupport.middleEdgePairFace i j).toOrderHom)) inverse i j

/-- Pl is compared only on these eight primitive supports, never a globally ordered column. -/
theorem laurent_side_primitive_monotone (inverse : Bool) (i : Fin 4) (j : Fin 2) :
    Monotone (laurentPolynomialSideIndex (productProjectionFace inverse) ∘
      (chartSideEdgeFace i j).toOrderHom) :=
  (by decide : ∀ inverse : Bool, ∀ i : Fin 4, ∀ j : Fin 2,
    Monotone (laurentPolynomialSideIndex (productProjectionFace inverse) ∘
      (chartSideEdgeFace i j).toOrderHom)) inverse i j

/-- The primitive transposed inclusion respects both independent original edge coordinates. -/
theorem chart_side_edge_index (i : Fin 4) (j : Fin 2) (k l : Fin 2) :
    (chartSideEdgeFace i j).toOrderHom (Quillen.SimplexGrid.index 1 1 (k, l)) =
      Quillen.SimplexGrid.index 4 2
        ((BassH1Support.edgeFace i).toOrderHom k,
          (BassMPrimitiveSupport.coefficientEdgeFace j).toOrderHom l) := by
  fin_cases k <;> fin_cases l <;> rfl

/-- Every whole Pl parameter value belongs to an original four-node primitive product support. -/
theorem chart_side_primitive_support (s t : unitInterval) :
    ∃ (i : Fin 4) (j : Fin 2) (z : StdSimplex ℝ (Fin 4)),
      StdSimplex.map (chartSideEdgeFace i j).toOrderHom z =
        Quillen.SimplexGrid.parameter.{u + 1} 4 2
          (NativeSquareFiveSimplex.parameter s, binaryPath (k := 2) 0 1 2 t) := by
  obtain ⟨i, z, hz⟩ := BassH1Support.square_path_in s
  obtain ⟨j, y, hy⟩ := BassMPrimitiveSupport.coefficient_path_in t
  refine ⟨i, j, Quillen.SimplexGrid.parameter.{u + 1} 1 1 (z, y), ?_⟩
  have h := Quillen.SimplexGrid.parameter_productMap.{u + 1}
    (BassH1Support.edgeFace i) (BassMPrimitiveSupport.coefficientEdgeFace j)
    (chartSideEdgeFace i j) (chart_side_edge_index i j) z y
  exact h.symm.trans (congrArg (Quillen.SimplexGrid.parameter.{u + 1} 4 2) (Prod.ext hz hy))

/-- All fifteen original plus polynomial seam nodes with both canonical references. -/
theorem polynomial_plus_composition_side_nodes (k : Fin 15) :
    polynomialProductNodes P u v w (underToLaurent R) (laurentPlus_projection P c)
      (polynomialSideIndex 0 k) =
    coefficientPrismNodes P u v w
      (coefficientChartSideIndex BassH0Diagram.plusFace k) := by
  obtain ⟨⟨i, j⟩, rfl⟩ := (Quillen.SimplexGrid.indexEquiv 2 4).surjective k
  rw [← Quillen.SimplexGrid.index_eq_equiv]
  simp only [polynomialSideIndex, coefficientChartSideIndex, productSideRow,
    Quillen.SimplexGrid.decode_index]
  exact polynomial_coefficient_side_nodes P u v w (underToLaurent R) (laurentPlus_projection P c)
    BassH0Diagram.plusFace (BassH0Diagram.plus_nodes P w) i j

/-- All fifteen original minus polynomial seam nodes with both canonical references. -/
theorem polynomial_minus_composition_side_nodes (k : Fin 15) :
    polynomialProductNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P c)
      (polynomialSideIndex 0 k) =
    coefficientPrismNodes P u v w
      (coefficientChartSideIndex BassH0Diagram.minusFace k) := by
  obtain ⟨⟨i, j⟩, rfl⟩ := (Quillen.SimplexGrid.indexEquiv 2 4).surjective k
  rw [← Quillen.SimplexGrid.index_eq_equiv]
  simp only [polynomialSideIndex, coefficientChartSideIndex, productSideRow,
    Quillen.SimplexGrid.decode_index]
  exact polynomial_coefficient_side_nodes P u v w (underToLaurentInvert R)
    (laurentMinus_projection P c)
    BassH0Diagram.minusFace (BassH0Diagram.minus_nodes P w) i j

/-- All fifteen original plus chart seam nodes with both canonical references. -/
theorem chart_plus_composition_side_nodes (k : Fin 15) :
    chartProductNodes P u v w (underToLaurent R) (laurentPlus_projection P d)
      (chartSideIndex 1 k) =
    laurentPrismNodes P u v w
      (laurentPolynomialSideIndex BassH0Diagram.plusFace k) := by
  obtain ⟨⟨i, j⟩, rfl⟩ := (Quillen.SimplexGrid.indexEquiv 4 2).surjective k
  rw [← Quillen.SimplexGrid.index_eq_equiv]
  simp only [chartSideIndex, laurentPolynomialSideIndex, productSideRow,
    Quillen.SimplexGrid.decode_index]
  exact (chart_laurent_side_nodes P u v w (underToLaurent R)
    (laurentPlus_projection P a) (laurentPlus_projection P b) (laurentPlus_projection P d)
    BassH0Diagram.plusFace (BassH0Diagram.plus_nodes P u) i j).symm

/-- All fifteen original minus chart seam nodes with both canonical references. -/
theorem chart_minus_composition_side_nodes (k : Fin 15) :
    chartProductNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P d)
      (chartSideIndex 1 k) =
    laurentPrismNodes P u v w
      (laurentPolynomialSideIndex BassH0Diagram.minusFace k) := by
  obtain ⟨⟨i, j⟩, rfl⟩ := (Quillen.SimplexGrid.indexEquiv 4 2).surjective k
  rw [← Quillen.SimplexGrid.index_eq_equiv]
  simp only [chartSideIndex, laurentPolynomialSideIndex, productSideRow,
    Quillen.SimplexGrid.decode_index]
  exact (chart_laurent_side_nodes P u v w (underToLaurentInvert R)
    (laurentMinus_projection P a) (laurentMinus_projection P b) (laurentMinus_projection P d)
    BassH0Diagram.minusFace (BassH0Diagram.minus_nodes P u) i j).symm



/-- Entire original plus side attached to its canonical Pc/Pl characteristic map.
Only the original eight primitive supports are used for the enclosing relabeling. -/
theorem polynomial_plus_composition_side (q s : unitInterval) :
    polynomialProductPrism P u v w (underToLaurent R) (laurentPlus_projection P c) false ![q, s,
      1] =
      CommonReferenceNerve.parameter _ (coefficientPrismNodes P u v w)
        (StdSimplex.map (coefficientChartSideIndex BassH0Diagram.plusFace)
          (Quillen.SimplexGrid.parameter.{u + 1} 2 4
            (binaryPath (k := 2) 0 1 2 q, NativeSquareFiveSimplex.parameter s))) := by
  rw [polynomial_product_plus_t1_raw]
  refine (polynomial_side_parameter _
    (polynomialProductNodes P u v w (underToLaurent R) (laurentPlus_projection P c)) 0
    (binaryPath (k := 2) 0 1 2 q) (NativeSquareFiveSimplex.parameter s)).trans ?_
  obtain ⟨i, j, z, hz⟩ := BassMPrimitiveSupport.middle_support q s
  change StdSimplex.map (BassMPrimitiveSupport.middleEdgePairFace i j).toOrderHom z =
    Quillen.SimplexGrid.parameter.{u + 1} 2 4 (binaryPath (k := 2) 0 1 2 q,
      NativeSquareFiveSimplex.parameter s) at hz
  rw [← hz]
  exact (CommonReferenceNerve.parameter_supported _ _ _
    (coefficientChartSideIndex BassH0Diagram.plusFace)
    (fun k ↦ (polynomial_plus_composition_side_nodes P u v w k).symm)
    (BassMPrimitiveSupport.middleEdgePairFace i j) (coefficient_side_primitive_monotone false i j)
      z).symm

/-- Entire original minus side attached to its canonical Pc/Pl characteristic map.
Only the original eight primitive supports are used for the enclosing relabeling. -/
theorem polynomial_minus_composition_side (q s : unitInterval) :
    polynomialProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P c) true
      ![q, s, 0] =
      CommonReferenceNerve.parameter _ (coefficientPrismNodes P u v w)
        (StdSimplex.map (coefficientChartSideIndex BassH0Diagram.minusFace)
          (Quillen.SimplexGrid.parameter.{u + 1} 2 4
            (binaryPath (k := 2) 0 1 2 q, NativeSquareFiveSimplex.parameter s))) := by
  rw [polynomial_product_minus_t0_raw]
  refine (polynomial_side_parameter _
    (polynomialProductNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P c)) 0
    (binaryPath (k := 2) 0 1 2 q) (NativeSquareFiveSimplex.parameter s)).trans ?_
  obtain ⟨i, j, z, hz⟩ := BassMPrimitiveSupport.middle_support q s
  change StdSimplex.map (BassMPrimitiveSupport.middleEdgePairFace i j).toOrderHom z =
    Quillen.SimplexGrid.parameter.{u + 1} 2 4 (binaryPath (k := 2) 0 1 2 q,
      NativeSquareFiveSimplex.parameter s) at hz
  rw [← hz]
  exact (CommonReferenceNerve.parameter_supported _ _ _
    (coefficientChartSideIndex BassH0Diagram.minusFace)
    (fun k ↦ (polynomial_minus_composition_side_nodes P u v w k).symm)
    (BassMPrimitiveSupport.middleEdgePairFace i j) (coefficient_side_primitive_monotone true i j)
      z).symm

/-- Entire original plus side attached to its canonical Pc/Pl characteristic map.
Only the original eight primitive supports are used for the enclosing relabeling. -/
theorem chart_plus_composition_side (q s : unitInterval) :
    chartProductPrism P u v w (underToLaurent R) (laurentPlus_projection P d) false ![q, 0, s] =
      CommonReferenceNerve.parameter _ (laurentPrismNodes P u v w)
        (StdSimplex.map (laurentPolynomialSideIndex BassH0Diagram.plusFace)
          (Quillen.SimplexGrid.parameter.{u + 1} 4 2
            (NativeSquareFiveSimplex.parameter (s), binaryPath (k := 2) 0 1 2 q))) := by
  rw [chart_product_plus_s0_raw]
  refine (chart_side_parameter _
    (chartProductNodes P u v w (underToLaurent R) (laurentPlus_projection P d)) 1
    (NativeSquareFiveSimplex.parameter (s)) (binaryPath (k := 2) 0 1 2 q)).trans ?_
  obtain ⟨i, j, z, hz⟩ := chart_side_primitive_support (s) q
  change StdSimplex.map (chartSideEdgeFace i j).toOrderHom z =
    Quillen.SimplexGrid.parameter.{u + 1} 4 2 (NativeSquareFiveSimplex.parameter (s), binaryPath
      (k := 2) 0 1 2 q) at hz
  rw [← hz]
  exact (CommonReferenceNerve.parameter_supported _ _ _
    (laurentPolynomialSideIndex BassH0Diagram.plusFace)
    (fun k ↦ (chart_plus_composition_side_nodes P u v w k).symm)
    (chartSideEdgeFace i j) (laurent_side_primitive_monotone false i j) z).symm

/-- Entire original minus side attached to its canonical Pc/Pl characteristic map.
Only the original eight primitive supports are used for the enclosing relabeling. -/
theorem chart_minus_composition_side (q s : unitInterval) :
    chartProductPrism P u v w (underToLaurentInvert R) (laurentMinus_projection P d) true ![q, 0,
      s] =
      CommonReferenceNerve.parameter _ (laurentPrismNodes P u v w)
        (StdSimplex.map (laurentPolynomialSideIndex BassH0Diagram.minusFace)
          (Quillen.SimplexGrid.parameter.{u + 1} 4 2
            (NativeSquareFiveSimplex.parameter (unitInterval.symm s), binaryPath (k := 2) 0 1 2
              q))) := by
  rw [chart_product_minus_s0_raw]
  refine (chart_side_parameter _
    (chartProductNodes P u v w (underToLaurentInvert R) (laurentMinus_projection P d)) 1
    (NativeSquareFiveSimplex.parameter (unitInterval.symm s))
    (binaryPath (k := 2) 0 1 2 q)).trans ?_
  obtain ⟨i, j, z, hz⟩ := chart_side_primitive_support (unitInterval.symm s) q
  change StdSimplex.map (chartSideEdgeFace i j).toOrderHom z =
    Quillen.SimplexGrid.parameter.{u + 1} 4 2 (NativeSquareFiveSimplex.parameter
      (unitInterval.symm s), binaryPath (k := 2) 0 1 2 q) at hz
  rw [← hz]
  exact (CommonReferenceNerve.parameter_supported _ _ _
    (laurentPolynomialSideIndex BassH0Diagram.minusFace)
    (fun k ↦ (chart_minus_composition_side_nodes P u v w k).symm)
    (chartSideEdgeFace i j) (laurent_side_primitive_monotone true i j) z).symm



/-- A fixed original square endpoint; inverse time chooses the other endpoint explicitly. -/
def productSquareEndpoint (e : Fin 2) : Fin 5 := ![2, 4] e

/-- The raw eighteen-node polynomial side retains the actual square endpoint reference. -/
def polynomialFixedSideAnchor
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (e : Fin 2) :=
  polynomialProductAnchor P u v w α hc ≪≫
    isoWhiskerLeft (movingSquareSource P (polynomialUnderCoefficient R) u v).functor
      (CoefficientSquareFamilies.chartNodes P w α (productSquareEndpoint e)).2

/-- The raw chart side preserves the polynomial endpoint's full original reference. -/
def chartFixedSideAnchor
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (e : Fin 2) :=
  chartProductAnchor P u v w α hd ≪≫
    isoWhiskerRight (CoefficientSquareFamilies.polynomialNodes P u
      (productSquareEndpoint e)).2 (movingSquareSource P α v w).functor

/-- Every raw polynomial side node, including its specified anchor, is the fixed postcomposition. -/
theorem polynomial_fixed_side_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (e : Fin 2) (i : Fin 18) :
    polynomialProductNodes P u v w α hc
      (Quillen.SimplexGrid.index 17 4 (i, productSquareEndpoint e)) =
    postReferenceNode _
      (CoefficientSquareFamilies.chartNodes P w α (productSquareEndpoint e)).1
      (polynomialFixedSideAnchor P u v w α hc e)
      (movingSquareNodes P (polynomialUnderCoefficient R) u v i) :=
  product_column_nodes _ _ _ _ _ _ _ _ i (productSquareEndpoint e)

/-- Every raw chart side node is the original moving chart after fixed precomposition. -/
theorem chart_fixed_side_nodes
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (e : Fin 2) (i : Fin 18) :
    chartProductNodes P u v w α hd
      (Quillen.SimplexGrid.index 4 17 (productSquareEndpoint e, i)) =
    preReferenceNode _
      (CoefficientSquareFamilies.polynomialNodes P u (productSquareEndpoint e)).1
      (chartFixedSideAnchor P u v w α hd e)
      (movingSquareNodes P α v w i) :=
  product_row_nodes _ _ _ _ _ _ _ _ (productSquareEndpoint e) i



/-- Every whole side fixes the original basepoint, for either actual polynomial orientation. -/
theorem polynomial_product_side_point
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (z : Quillen.SimplexCubeExtension.Cube) (n : ℕ) :
    CommonReferenceNerve.prespectrumFamily _ (polynomialProductNodes P u v w α hc) n
      (polynomialProductParameter.{u} inverse z,
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).point n) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))).point n :=
  CommonReferenceNerve.prespectrumFamily_point _ _ n _

/-- All side coordinates and the inverse polynomial time stay independent of structure time. -/
theorem polynomial_product_side_structure
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (z : Quillen.SimplexCubeExtension.Cube) (n : ℕ)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n)
    (t : unitInterval) :
    CommonReferenceNerve.prespectrumFamily _ (polynomialProductNodes P u v w α hc) (n + 1)
      (polynomialProductParameter.{u} inverse z,
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).structureMap n x
          t) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))).structureMap n
        (CommonReferenceNerve.prespectrumFamily _ (polynomialProductNodes P u v w α hc) n
          (polynomialProductParameter.{u} inverse z, x)) t :=
  CommonReferenceNerve.prespectrumFamily_structure _ _ n _ x t

/-- Every whole side fixes the original basepoint, for either actual polynomial orientation. -/
theorem chart_product_side_point
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (z : Quillen.SimplexCubeExtension.Cube) (n : ℕ) :
    CommonReferenceNerve.prespectrumFamily _ (chartProductNodes P u v w α hd) n
      (chartProductParameter.{u} inverse z,
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).point n) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))).point n :=
  CommonReferenceNerve.prespectrumFamily_point _ _ n _

/-- All side coordinates and the inverse polynomial time stay independent of structure time. -/
theorem chart_product_side_structure
    (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (z : Quillen.SimplexCubeExtension.Cube) (n : ℕ)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).space n)
    (t : unitInterval) :
    CommonReferenceNerve.prespectrumFamily _ (chartProductNodes P u v w α hd) (n + 1)
      (chartProductParameter.{u} inverse z,
        (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))).structureMap n x
          t) =
    (prespectrum (modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj d))))).structureMap n
        (CommonReferenceNerve.prespectrumFamily _ (chartProductNodes P u v w α hd) n
          (chartProductParameter.{u} inverse z, x)) t :=
  CommonReferenceNerve.prespectrumFamily_structure _ _ n _ x t

end Quillen.PerfectComplexes.BassMWholeNerve
