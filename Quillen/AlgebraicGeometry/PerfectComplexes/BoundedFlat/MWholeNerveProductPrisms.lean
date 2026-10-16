/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Naturality

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientMovingSquareReferenceRows
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeNerveCompositionPrisms

/-!
# Actual finite-product correction prisms

The original eighteen-node moving square and five-node chart square form the literal
ninety-node products in the same full-reference nerve. The two geometric source transports,
original moving-square collapse, chart paths and separate inverse polynomial time are retained.
Complete terminal and side attachments are subsequent declarations in their own owners.
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

private theorem reanchored_product_simplex {V W T : Model.{u}} {p q : ℕ}
    (F : V ⟶ T) (F₀ : V ⟶ W) (Fs : Fin (p + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.functor ≅ (Fs i).functor)
    (G₀ : W ⟶ T) (Gs : Fin (q + 1) → (W ⟶ T))
    (refs : ∀ i, G₀.functor ≅ (Gs i).functor) (η : F.functor ≅ (F₀ ≫ G₀).functor) :
    ModelSimplex.ofIsos F (fun i ↦ (reanchoredProductNode F F₀ Fs ρ G₀ Gs refs η i).1)
      (fun i ↦ (reanchoredProductNode F F₀ Fs ρ G₀ Gs refs η i).2) =
      CommonReferenceProduct.simplex F₀ Fs ρ G₀ Gs refs := by
  exact ModelSimplex.reanchorSimplex_eq η
    (fun i ↦ ⟨CommonReferenceProduct.vertices Fs Gs i,
      CommonReferenceProduct.references F₀ Fs ρ G₀ Gs refs i⟩)

private theorem reanchored_product_comp {V W T : Model.{u}} {p q : ℕ}
    (F : V ⟶ T) (F₀ : V ⟶ W) (Fs : Fin (p + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.functor ≅ (Fs i).functor)
    (G₀ : W ⟶ T) (Gs : Fin (q + 1) → (W ⟶ T))
    (refs : ∀ i, G₀.functor ≅ (Gs i).functor) (η : F.functor ≅ (F₀ ≫ G₀).functor)
    (n : ℕ) (x : (prespectrum V).space n)
    (z : StdSimplex ℝ (Fin (p + 1))) (w : StdSimplex ℝ (Fin (q + 1))) :
    prespectrumSimplexFamily
      (ModelSimplex.ofIsos F (fun i ↦ (reanchoredProductNode F F₀ Fs ρ G₀ Gs refs η i).1)
        (fun i ↦ (reanchoredProductNode F F₀ Fs ρ G₀ Gs refs η i).2)) n
      (Quillen.SimplexGrid.parameter.{u} p q (z, w), x) =
      prespectrumSimplexFamily (ModelSimplex.ofIsos G₀ Gs refs) n
        (w, prespectrumSimplexFamily (ModelSimplex.ofIsos F₀ Fs ρ) n (z, x)) :=
  (congrArg (fun S ↦ prespectrumSimplexFamily S n
    (Quillen.SimplexGrid.parameter.{u} p q (z, w), x))
    (reanchored_product_simplex F F₀ Fs ρ G₀ Gs refs η)).trans
      (CommonReferenceProduct.prespectrum_comp F₀ Fs ρ G₀ Gs refs n x z w)

variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The actual source of the unchanged coefficient moving-square simplex. -/
abbrev movingSquareSource {M N : Under R ⥤ Under R} (α : M ⟶ N)
    {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c) :=
  NormalizedTripleSimplex.sourceMap (coefficientMap P (α.app c))
    (coefficientMap P (M.map v)) (coefficientMap P (M.map u))

/-- Every full dependent node of that same original eighteen-node simplex. -/
abbrev movingSquareNodes {M N : Under R ⥤ Under R} (α : M ⟶ N)
    {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c) :=
  DoubleSquareMergedSimplex.nodes
    (coefficientMap P (M.map u)) (coefficientMap P (M.map v))
    (coefficientMap P (N.map u)) (coefficientMap P (N.map v))
    (coefficientMap P (α.app a)) (coefficientMap P (α.app b))
    (coefficientMap P (α.app c))
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α u).symm
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P α v).symm

variable {a b c d : Under R} (u : a ⟶ b) (v : b ⟶ c) (w : c ⟶ d)
  (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)

/-- The original common H0 reference has this exact right-associated geometric total. -/
theorem tripleProductTotal :
    laurentProjection P d ≫ coefficientMap P w ≫ coefficientMap P v ≫ coefficientMap P u =
      coefficientMap P ((laurentUnderFunctor R).map ((u ≫ v) ≫ w)) ≫ laurentProjection P a := by
  have h := (BassH0Merge.total P (u ≫ v) w).symm
  rw [coefficientMap_comp] at h
  exact h

/-- The moving polynomial square followed by the chart retains its actual geometric source. -/
theorem polynomialProductTotal
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    (coefficientMap P ((laurentUnderFunctor R).map w) ≫ coefficientMap P (α.app c)) ≫
      (polynomialProjection P c ≫ coefficientMap P v ≫ coefficientMap P u) =
        coefficientMap P ((laurentUnderFunctor R).map ((u ≫ v) ≫ w)) ≫ laurentProjection P a := by
  have h := AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
    (laurentUnderCoefficient R) w
  change coefficientMap P ((laurentUnderFunctor R).map w) ≫ laurentProjection P c =
    laurentProjection P d ≫ coefficientMap P w at h
  calc
    _ = (coefficientMap P ((laurentUnderFunctor R).map w) ≫
        (coefficientMap P (α.app c) ≫ polynomialProjection P c)) ≫
          coefficientMap P v ≫ coefficientMap P u := by simp only [Category.assoc]
    _ = _ := by rw [hc, h, Category.assoc]; exact tripleProductTotal P u v w

/-- The chart moving square after the polynomial square has the same original total. -/
theorem chartProductTotal
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d) :
    (coefficientMap P (α.app d) ≫ coefficientMap P ((polynomialUnderFunctor R).map w) ≫
      coefficientMap P ((polynomialUnderFunctor R).map v)) ≫
        (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a) =
      coefficientMap P ((laurentUnderFunctor R).map ((u ≫ v) ≫ w)) ≫ laurentProjection P a := by
  have h := AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
    (polynomialUnderCoefficient R) ((u ≫ v) ≫ w)
  change coefficientMap P ((polynomialUnderFunctor R).map ((u ≫ v) ≫ w)) ≫
    polynomialProjection P a = polynomialProjection P d ≫ coefficientMap P ((u ≫ v) ≫ w) at h
  simp only [Functor.map_comp, coefficientMap_comp, Category.assoc] at h
  calc
    _ = coefficientMap P (α.app d) ≫
        (coefficientMap P ((polynomialUnderFunctor R).map w) ≫
          coefficientMap P ((polynomialUnderFunctor R).map v) ≫
          coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a) := by
      simp only [Category.assoc]
    _ = _ := by rw [h, ← Category.assoc, hd]; exact tripleProductTotal P u v w

/-- The first actual product anchor contains the displayed geometric equality transport. -/
def polynomialProductAnchor
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    (BassH0Diagram.reference P ((u ≫ v) ≫ w)).functor ≅
      (movingSquareSource P (polynomialUnderCoefficient R) u v ≫
        CoefficientSquareFamilies.chartSource P w α).functor :=
  smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
    (polynomialProductTotal P u v w α hc).symm) ≪≫ boundedFlatNormalizedPullbackCompIso
      (coefficientMap P ((laurentUnderFunctor R).map w) ≫ coefficientMap P (α.app c))
      (polynomialProjection P c ≫ coefficientMap P v ≫ coefficientMap P u))

/-- The second actual product anchor retains its separate source factorization. -/
def chartProductAnchor
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d) :
    (BassH0Diagram.reference P ((u ≫ v) ≫ w)).functor ≅
      (CoefficientSquareFamilies.polynomialSource P u ≫ movingSquareSource P α v w).functor :=
  smallIso (eqToIso (congrArg boundedFlatNormalizedPullback
    (chartProductTotal P u v w α hd).symm) ≪≫ boundedFlatNormalizedPullbackCompIso
      (coefficientMap P (α.app d) ≫ coefficientMap P ((polynomialUnderFunctor R).map w) ≫
        coefficientMap P ((polynomialUnderFunctor R).map v))
      (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a))

/-- All ninety full reference nodes of the original moving-polynomial/chart product. -/
def polynomialProductNodes
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    Fin 90 → CommonReferenceNerve.Node (BassH0Diagram.reference P ((u ≫ v) ≫ w)) :=
  reanchoredProductNode _ (movingSquareSource P (polynomialUnderCoefficient R) u v)
    (fun i ↦ (movingSquareNodes P (polynomialUnderCoefficient R) u v i).1)
    (fun i ↦ (movingSquareNodes P (polynomialUnderCoefficient R) u v i).2)
    (CoefficientSquareFamilies.chartSource P w α)
    (fun i ↦ (CoefficientSquareFamilies.chartNodes P w α i).1)
    (fun i ↦ (CoefficientSquareFamilies.chartNodes P w α i).2)
    (polynomialProductAnchor P u v w α hc)

/-- All ninety full reference nodes of the original polynomial/moving-chart product. -/
def chartProductNodes
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d) :
    Fin 90 → CommonReferenceNerve.Node (BassH0Diagram.reference P ((u ≫ v) ≫ w)) :=
  reanchoredProductNode _ (CoefficientSquareFamilies.polynomialSource P u)
    (fun i ↦ (CoefficientSquareFamilies.polynomialNodes P u i).1)
    (fun i ↦ (CoefficientSquareFamilies.polynomialNodes P u i).2)
    (movingSquareSource P α v w)
    (fun i ↦ (movingSquareNodes P α v w i).1) (fun i ↦ (movingSquareNodes P α v w i).2)
    (chartProductAnchor P u v w α hd)

/-- The inverse chart reverses only the original independent polynomial coordinate. -/
def productPolynomialTime (inverse : Bool) : C(unitInterval, unitInterval) :=
  if inverse then ⟨unitInterval.symm, by fun_prop⟩ else ContinuousMap.id _

/-- The unchanged moving-polynomial collapse and chart path form the actual finite grid. -/
def polynomialProductParameter (inverse : Bool) :
    C(Quillen.SimplexCubeExtension.Cube, StdSimplex ℝ (Fin 90)) :=
  ⟨fun z ↦ Quillen.SimplexGrid.parameter.{u + 1} 17 4
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter
      (z 0, productPolynomialTime inverse (z 2)), NativeSquareFiveSimplex.parameter (z 1)),
    by fun_prop⟩

/-- The unchanged polynomial path and moving-chart collapse retain the other product order. -/
def chartProductParameter (inverse : Bool) :
    C(Quillen.SimplexCubeExtension.Cube, StdSimplex ℝ (Fin 90)) :=
  ⟨fun z ↦ Quillen.SimplexGrid.parameter.{u + 1} 4 17
    (NativeSquareFiveSimplex.parameter (productPolynomialTime inverse (z 2)),
      DoubleSquareScalarPaths.coefficientMovingSquareParameter (z 0, z 1)), by fun_prop⟩

/-- The first actual product prism in the common full-reference nerve. -/
def polynomialProductPrism
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) : C(Quillen.SimplexCubeExtension.Cube,
      |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|) :=
  (CommonReferenceNerve.parameter _ (polynomialProductNodes P u v w α hc)).comp
    (polynomialProductParameter.{u} inverse)

/-- The second actual product prism in the same full-reference nerve. -/
def chartProductPrism
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) : C(Quillen.SimplexCubeExtension.Cube,
      |nerve (Codiscrete (CommonReferenceNerve.Node
        (BassH0Diagram.reference P ((u ≫ v) ≫ w))))|) :=
  (CommonReferenceNerve.parameter _ (chartProductNodes P u v w α hd)).comp
    (chartProductParameter.{u} inverse)

/-- Every level retains the entire original moving polynomial square before the chart square. -/
theorem polynomial_product_native
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (n : ℕ) (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.prespectrumFamily _ (polynomialProductNodes P u v w α hc) n
      (polynomialProductParameter.{u} inverse ![q, s, t], x) =
      (CoefficientTransformationComposition.square P α w).level n
        (s, (CoefficientTransformationComposition.movingSquare P (polynomialUnderCoefficient R)
          u v).level n (q, (productPolynomialTime inverse t, x))) := by
  rw [CommonReferenceNerve.prespectrumFamily_eq]
  refine (reanchored_product_comp _ _ _ _ _ _ _ (polynomialProductAnchor P u v w α hc)
    n x (DoubleSquareScalarPaths.coefficientMovingSquareParameter
      (q, productPolynomialTime inverse t)) (NativeSquareFiveSimplex.parameter s)).trans ?_
  change prespectrumSimplexFamily (CoefficientSquareFamilies.chartSimplex P w α) n
    (NativeSquareFiveSimplex.parameter s,
      prespectrumSimplexFamily (CoefficientTransformationComposition.Scalar.simplex
        P (polynomialUnderCoefficient R) u v) n
          (DoubleSquareScalarPaths.coefficientMovingSquareParameter
            (q, productPolynomialTime inverse t), x)) = _
  rw [CoefficientTransformationComposition.Scalar.movingSquare_native]
  exact NativeSquareFiveSimplex.native _ _ _ _ _ n s _

/-- Every level retains the entire original chart moving square after the polynomial square. -/
theorem chart_product_native
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (n : ℕ) (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.prespectrumFamily _ (chartProductNodes P u v w α hd) n
      (chartProductParameter.{u} inverse ![q, s, t], x) =
      (CoefficientTransformationComposition.movingSquare P α v w).level n
        (q, (s, (boundedFlatCoefficientPolynomialSquareHomotopy P u).level n
          (productPolynomialTime inverse t, x))) := by
  rw [CommonReferenceNerve.prespectrumFamily_eq]
  refine (reanchored_product_comp _ _ _ _ _ _ _ (chartProductAnchor P u v w α hd)
    n x (NativeSquareFiveSimplex.parameter (productPolynomialTime inverse t))
      (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, s))).trans ?_
  change prespectrumSimplexFamily (CoefficientTransformationComposition.Scalar.simplex P α v w) n
    (DoubleSquareScalarPaths.coefficientMovingSquareParameter (q, s),
      prespectrumSimplexFamily (CoefficientSquareFamilies.polynomialSimplex P u) n
        (NativeSquareFiveSimplex.parameter (productPolynomialTime inverse t), x)) = _
  rw [CoefficientSquareFamilies.polynomial_native,
    CoefficientTransformationComposition.Scalar.movingSquare_native]

/-- Compact evaluation recovers this entire finite polynomial product at every original level. -/
theorem polynomial_product_compact_native
    (hc : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c)
    (inverse : Bool) (n : ℕ) (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (polynomialProductPrism P u v w α hc inverse) n
      (![q, s, t], x) =
      (CoefficientTransformationComposition.square P α w).level n
        (s, (CoefficientTransformationComposition.movingSquare P (polynomialUnderCoefficient R)
          u v).level n (q, (productPolynomialTime inverse t, x))) :=
  (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _
    (polynomialProductPrism P u v w α hc inverse) (polynomialProductNodes P u v w α hc)
    ![q, s, t] (polynomialProductParameter.{u} inverse ![q, s, t]) rfl n x).trans
      (polynomial_product_native P u v w α hc inverse n q s t x)

/-- Compact evaluation recovers the other entire finite product with unchanged coordinate order. -/
theorem chart_product_compact_native
    (hd : coefficientMap P (α.app d) ≫ polynomialProjection P d = laurentProjection P d)
    (inverse : Bool) (n : ℕ) (q s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    CommonReferenceNerve.compactPrespectrumFamily _ (chartProductPrism P u v w α hd inverse) n
      (![q, s, t], x) =
      (CoefficientTransformationComposition.movingSquare P α v w).level n
        (q, (s, (boundedFlatCoefficientPolynomialSquareHomotopy P u).level n
          (productPolynomialTime inverse t, x))) :=
  (CommonReferenceNerve.compactPrespectrumFamily_eq_simplex _
    (chartProductPrism P u v w α hd inverse) (chartProductNodes P u v w α hd)
    ![q, s, t] (chartProductParameter.{u} inverse ![q, s, t]) rfl n x).trans
      (chart_product_native P u v w α hd inverse n q s t x)

end Quillen.PerfectComplexes.BassMWholeNerve
