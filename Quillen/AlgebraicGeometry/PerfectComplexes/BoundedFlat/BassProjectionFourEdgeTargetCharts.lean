/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH0ChartBoundaryRows
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetOverlap
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionWholeReferenceAttachments
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFiniteEdge

/-!
# Genuine polynomial-source target charts and the two outer overlap seams

Each chart is the original five-node square family on the entire polynomial reference nerve.
The prescribed H0 reference is reached through the full projection anchor. Product association
identifies both outer seams on complete dependent nodes before realization. The comparison
time and both distinct chart equality transports remain unchanged.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u

namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
open BassH0Merge CommonReferenceNerve

private theorem parameter_source_map {V W W' T : Model.{u}}
    (E : V ⟶ W) (D : V ⟶ W') (F : V ⟶ T) {q : ℕ}
    (h : CommonReferenceNerve.Node E → CommonReferenceNerve.Node D)
    (g : CommonReferenceNerve.Node D → Fin (q + 1) → CommonReferenceNerve.Node F)
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|)
    (z : StdSimplex ℝ (Fin (q + 1))) :
    FiniteParameter.parameter D F g (mapParameter h y, z) =
      FiniteParameter.parameter E F (fun e i ↦ g (h e) i) (y, z) := by
  obtain ⟨k, N, w, rfl⟩ := exists_parameter E y
  rw [mapParameter_parameter, FiniteParameter.parameter_characteristic,
    FiniteParameter.parameter_characteristic]
  rfl

private theorem product_projection {V W W' T : Model.{u}}
    (E : V ⟶ W) (K : W ⟶ T) (J : W ⟶ W') (H : W' ⟶ T)
    (θ : K.functor ≅ (J ≫ H).functor)
    (N : CommonReferenceNerve.Node E) (M : CommonReferenceNerve.Node H) :
    CommonReferenceProduct.node (E ≫ K) (E ≫ J) H (isoWhiskerLeft E.functor θ)
      (postcompNode J N) M =
    CommonReferenceProduct.node (E ≫ K) E K (Iso.refl _) N
      (preReferenceNode K J θ M) := by
  have h₁ := CommonReferenceProduct.node_associativity (E ≫ K) E J H
    (isoWhiskerLeft E.functor θ) N M
  have h₂ := CommonReferenceProduct.node_second_reanchor (E ≫ K) E K (J ≫ H)
    θ (Iso.refl _) N (precompNode J M)
  simp only [CommonReferenceProduct.postNode, CommonReferenceProduct.preNode,
    CommonReferenceProduct.reanchor, Iso.refl_trans] at h₁ h₂
  exact h₁.trans h₂.symm

variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (ha : coefficientMap P (α.app a) ≫ polynomialProjection P a = laurentProjection P a)

/-- The target chart uses the original H0 projection anchor with its complete left whiskering. -/
def chartAnchor : (reference P f E).functor ≅
    (polynomialReference P a E ≫ BassH0ChartBoundaryRows.squareSource P f α).functor :=
  isoWhiskerLeft E.functor (BassH0ChartBoundaryRows.canonicalAnchor P f α ha)

/-- Every polynomial node is composed with each original full chart-square node. -/
def chartNodes (M : CommonReferenceNerve.Node (polynomialReference P a E)) (i : Fin 5) :
    CommonReferenceNerve.Node (reference P f E) :=
  CommonReferenceProduct.node (reference P f E) (polynomialReference P a E)
    (BassH0ChartBoundaryRows.squareSource P f α) (chartAnchor P f E α ha) M
    (BassH0ChartBoundaryRows.squareNodes P f α i)

/-- The genuine whole polynomial-source chart retains the original reversed-binary square time. -/
def chart : C(|nerve (Codiscrete (CommonReferenceNerve.Node (polynomialReference P a E)))| × I,
    |nerve (Codiscrete (CommonReferenceNerve.Node (reference P f E)))|) :=
  (FiniteParameter.parameter (polynomialReference P a E) (reference P f E)
    (chartNodes P f E α ha)).comp
      ⟨fun z ↦ (z.1, NativeSquareFiveSimplex.parameter z.2), by fun_prop⟩

/-- Every full polynomial-source chain retains its exact product-simplex parameter. -/
theorem chart_characteristic {k : ℕ}
    (M : Fin (k + 1) → CommonReferenceNerve.Node (polynomialReference P a E))
    (z : StdSimplex ℝ (Fin (k + 1))) (s : I) :
    chart P f E α ha (CommonReferenceNerve.parameter (polynomialReference P a E) M z, s) =
    CommonReferenceNerve.parameter (reference P f E)
      (FiniteParameter.gridNodes (polynomialReference P a E) (reference P f E)
        (chartNodes P f E α ha) M)
      (SimplexGrid.parameter.{u + 1} k 4 (z, NativeSquareFiveSimplex.parameter s)) :=
  FiniteParameter.parameter_characteristic (polynomialReference P a E) (reference P f E)
    (chartNodes P f E α ha) M z (NativeSquareFiveSimplex.parameter s)

/-- Product association retains the entire projection anchor and both complete input nodes. -/
theorem chart_polynomial_node (N : CommonReferenceNerve.Node E) (i : Fin 5) :
    chartNodes P f E α ha (postcompNode (normalizedMap (polynomialProjection P a)) N) i =
    CommonReferenceProduct.node (reference P f E) E (BassH0Diagram.reference P f)
      (Iso.refl _) N
      (BassH0ChartBoundaryRows.preNode P f α ha (BassH0ChartBoundaryRows.squareNodes P f α i)) :=
  product_projection E (BassH0Diagram.reference P f)
    (normalizedMap (polynomialProjection P a)) (BassH0ChartBoundaryRows.squareSource P f α)
    (BassH0ChartBoundaryRows.canonicalAnchor P f α ha) N _

/-- Every full positive product row agrees with the original left H0 row. -/
theorem chart_plus_nodes (N : CommonReferenceNerve.Node E) (i : Fin 5) :
    chartNodes P f E (underToLaurent R) (laurentPlus_projection P a)
      (postcompNode (normalizedMap (polynomialProjection P a)) N) i =
    nodes P f E N ((BassH0ChartBoundaryRows.rowFace ≫ BassH0Diagram.plusFace).toOrderHom i) := by
  rw [chart_polynomial_node, ← BassH0ChartBoundaryRows.plus_nodes]
  simp only [nodes, CommonReferenceProduct.node, Iso.refl_trans]

/-- Every full inverse product row retains its separate right H0 row and casts. -/
theorem chart_minus_nodes (N : CommonReferenceNerve.Node E) (i : Fin 5) :
    chartNodes P f E (underToLaurentInvert R) (laurentMinus_projection P a)
      (postcompNode (normalizedMap (polynomialProjection P a)) N) i =
    nodes P f E N ((BassH0ChartBoundaryRows.rowFace ≫ BassH0Diagram.minusFace).toOrderHom i) := by
  rw [chart_polynomial_node, ← BassH0ChartBoundaryRows.minus_nodes]
  simp only [nodes, CommonReferenceProduct.node, Iso.refl_trans]

/-- The complete positive chart attachment is the original whole left overlap seam. -/
theorem chart_plus_polynomial (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (s : I) :
    chart P f E (underToLaurent R) (laurentPlus_projection P a)
      (mapParameter (postcompNode (normalizedMap (polynomialProjection P a))) y, s) =
    overlap P f E (y, (s, 0)) := by
  change FiniteParameter.parameter (polynomialReference P a E) (reference P f E)
    (chartNodes P f E (underToLaurent R) (laurentPlus_projection P a))
    (mapParameter (postcompNode (normalizedMap (polynomialProjection P a))) y,
      NativeSquareFiveSimplex.parameter s) = _
  rw [parameter_source_map, overlap_left]
  have hn := funext (fun N ↦ funext (chart_plus_nodes P f E N))
  rw [hn, FiniteParameter.parameter_restrict]
  have hs := ProjectionRectangleSquareRows.chart_parameter BassH0Diagram.plusFace s
  change StdSimplex.map (BassH0ChartBoundaryRows.rowFace ≫ BassH0Diagram.plusFace).toOrderHom
    (NativeSquareFiveSimplex.parameter s) = _ at hs
  rw [hs]

/-- The complete inverse chart attachment is the original whole right overlap seam. -/
theorem chart_minus_polynomial (y : |nerve (Codiscrete (CommonReferenceNerve.Node E))|) (s : I) :
    chart P f E (underToLaurentInvert R) (laurentMinus_projection P a)
      (mapParameter (postcompNode (normalizedMap (polynomialProjection P a))) y, s) =
    overlap P f E (y, (s, 1)) := by
  change FiniteParameter.parameter (polynomialReference P a E) (reference P f E)
    (chartNodes P f E (underToLaurentInvert R) (laurentMinus_projection P a))
    (mapParameter (postcompNode (normalizedMap (polynomialProjection P a))) y,
      NativeSquareFiveSimplex.parameter s) = _
  rw [parameter_source_map, overlap_right]
  have hn := funext (fun N ↦ funext (chart_minus_nodes P f E N))
  rw [hn, FiniteParameter.parameter_restrict]
  have hs := ProjectionRectangleSquareRows.chart_parameter BassH0Diagram.minusFace s
  change StdSimplex.map (BassH0ChartBoundaryRows.rowFace ≫ BassH0Diagram.minusFace).toOrderHom
    (NativeSquareFiveSimplex.parameter s) = _ at hs
  rw [hs]

/-- Every finite polynomial source family evaluates as the actual chart square. -/
theorem chart_finite_native {k : ℕ}
    (M : Fin (k + 1) → CommonReferenceNerve.Node (polynomialReference P a E))
    (n : ℕ) (z : StdSimplex ℝ (Fin (k + 1))) (s : I) (x : (prespectrum V).space n) :
    prespectrumFamily (reference P f E)
      (FiniteParameter.gridNodes (polynomialReference P a E) (reference P f E)
        (chartNodes P f E α ha) M) n
      (SimplexGrid.parameter.{u + 1} k 4 (z, NativeSquareFiveSimplex.parameter s), x) =
    (boundedFlatPerfectPrespectrumSquareHomotopy
      (coefficientMap P ((laurentUnderFunctor R).map f)) (coefficientMap P (α.app a))
      (coefficientMap P (α.app b)) (coefficientMap P ((polynomialUnderFunctor R).map f))
      (coefficientMap_naturality P α f)).level n
      (s, prespectrumFamily (polynomialReference P a E) M n (z, x)) := by
  rw [prespectrumFamily_eq, prespectrumFamily_eq]
  have hs : ModelSimplex.ofIsos (reference P f E)
      (fun i ↦ (FiniteParameter.gridNodes (polynomialReference P a E) (reference P f E)
        (chartNodes P f E α ha) M i).1)
      (fun i ↦ (FiniteParameter.gridNodes (polynomialReference P a E) (reference P f E)
        (chartNodes P f E α ha) M i).2) =
      CommonReferenceProduct.simplex (polynomialReference P a E)
        (fun i ↦ (M i).1) (fun i ↦ (M i).2)
        (BassH0ChartBoundaryRows.squareSource P f α)
        (fun i ↦ (BassH0ChartBoundaryRows.squareNodes P f α i).1)
        (fun i ↦ (BassH0ChartBoundaryRows.squareNodes P f α i).2) :=
    ModelSimplex.ofIsos_change_reference (chartAnchor P f E α ha) _ _
  rw [hs, CommonReferenceProduct.prespectrum_comp]
  exact NativeSquareFiveSimplex.native _ _ _ _ _ n s _

/-- Whole polynomial inputs recover the actual chart square in every native degree. -/
theorem chart_native (n : ℕ)
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node (polynomialReference P a E)))|)
    (s : I) (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (reference P f E) n (chart P f E α ha (y, s)) x =
    (boundedFlatPerfectPrespectrumSquareHomotopy
      (coefficientMap P ((laurentUnderFunctor R).map f)) (coefficientMap P (α.app a))
      (coefficientMap P (α.app b)) (coefficientMap P ((polynomialUnderFunctor R).map f))
      (coefficientMap_naturality P α f)).level n
      (s, pointwisePrespectrumFamily (polynomialReference P a E) n y x) := by
  obtain ⟨k, M, z, hz⟩ := exists_parameter (polynomialReference P a E) y
  rw [← hz, chart_characteristic, pointwisePrespectrumFamily_parameter,
    pointwisePrespectrumFamily_parameter]
  exact chart_finite_native P f E α ha M n z s x

/-- The positive chart is the prescribed original positive square on every polynomial input. -/
theorem chart_plus_native (n : ℕ)
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node (polynomialReference P a E)))|)
    (s : I) (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (reference P f E) n
      (chart P f E (underToLaurent R) (laurentPlus_projection P a) (y, s)) x =
    (boundedFlatCoefficientPlusSquareHomotopy P f).level n
      (s, pointwisePrespectrumFamily (polynomialReference P a E) n y x) :=
  chart_native P f E (underToLaurent R) (laurentPlus_projection P a) n y s x

/-- The inverse chart is the prescribed original inverse square with its own equality cast. -/
theorem chart_minus_native (n : ℕ)
    (y : |nerve (Codiscrete (CommonReferenceNerve.Node (polynomialReference P a E)))|)
    (s : I) (x : (prespectrum V).space n) :
    pointwisePrespectrumFamily (reference P f E) n
      (chart P f E (underToLaurentInvert R) (laurentMinus_projection P a) (y, s)) x =
    (boundedFlatCoefficientMinusSquareHomotopy P f).level n
      (s, pointwisePrespectrumFamily (polynomialReference P a E) n y x) :=
  chart_native P f E (underToLaurentInvert R) (laurentMinus_projection P a) n y s x

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.Target
