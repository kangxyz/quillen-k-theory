/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSquareFamilies

/-! The four whole original component families of the prescribed H1 cylinder face. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange Quillen.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters Quillen.LoopPrespectrum
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH1Components

/-- Postcomposition retains every actual common-reference node and isomorphism. -/
theorem postcompose_reference {V W T : Model.{u}} {k : ℕ}
    (F₀ : V ⟶ W) (F : Fin (k + 1) → (V ⟶ W))
    (ρ : ∀ i, F₀.functor ≅ (F i).functor) (J : W ⟶ T) :
    (ModelSimplex.ofIsos F₀ F ρ).postcomp J =
      ModelSimplex.ofIsos (F₀ ≫ J) (fun i ↦ F i ≫ J)
        (fun i ↦ isoWhiskerRight (ρ i) J.functor) := by
  apply ModelSimplex.ext_diagram
  refine CategoryTheory.Functor.hext (fun _ ↦ rfl) ?_
  intro i j f
  apply heq_of_eq
  change whiskerRight ((ρ i).inv ≫ (ρ j).hom) J.functor =
    whiskerRight (ρ i).inv J.functor ≫ whiskerRight (ρ j).hom J.functor
  exact whiskerRight_comp _ _ _

variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

abbrev laurentMap := BassH0Merge.normalizedMap
  (coefficientMap P ((laurentUnderFunctor R).map v))
abbrev coefficientMapModel := BassH0Merge.normalizedMap (coefficientMap P u)

abbrev firstSource := BassH0Diagram.reference P u ≫ laurentMap P v

def firstNodes (i : Fin 31) :
    Σ F : modelOf (boundedFlatPerfectWaldhausen (space (op P, a))) ⟶
      modelOf (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj c))),
        (firstSource P u v).functor ≅ F.functor :=
  ⟨(BassH0Diagram.nodes P u i).1 ≫ laurentMap P v,
    isoWhiskerRight (BassH0Diagram.nodes P u i).2 (laurentMap P v).functor⟩

def firstSimplex := ModelSimplex.ofIsos (firstSource P u v)
  (fun i ↦ (firstNodes P u v i).1) (fun i ↦ (firstNodes P u v i).2)

theorem first_simplex_original : firstSimplex P u v =
    (BassH0Diagram.simplex P u).postcomp (laurentMap P v) :=
  (postcompose_reference _ _ _ _).symm

/-- Entire first H1 piece: H0(u) followed by the original Laurent coefficient map of v. -/
theorem first_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (firstSimplex P u v) n (BassH0Diagram.parameter (s, t), x) =
      ((boundedFlatCoefficientBassComparisonHomotopy P u).postcomp
        (boundedFlatPerfectPrespectrumMap
          (coefficientMap P ((laurentUnderFunctor R).map v)))).level n
        (s, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (t, x)) := by
  rw [first_simplex_original, prespectrumSimplexFamily_postcomp, BassH0Diagram.native]
  rfl

abbrev middleSource := coefficientMapModel P u ≫ BassH0Diagram.reference P v

def middleNodes (i : Fin 31) :
    Σ F : modelOf (boundedFlatPerfectWaldhausen (space (op P, a))) ⟶
      modelOf (boundedFlatPerfectWaldhausen (space (op P, (laurentUnderFunctor R).obj c))),
        (middleSource P u v).functor ≅ F.functor :=
  ⟨coefficientMapModel P u ≫ (BassH0Diagram.nodes P v i).1,
    isoWhiskerLeft (coefficientMapModel P u).functor (BassH0Diagram.nodes P v i).2⟩

def middleSimplex := ModelSimplex.ofIsos (middleSource P u v)
  (fun i ↦ (middleNodes P u v i).1) (fun i ↦ (middleNodes P u v i).2)

theorem middle_simplex_original : middleSimplex P u v =
    (BassH0Diagram.simplex P v).precomp (coefficientMapModel P u) :=
  (ModelSimplex.ofIsos_precomp _ _ _ _).symm

/-- The original middle cylinder piece, after the actual coefficient-u overlap map. -/
theorem middle_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (middleSimplex P u v) n (BassH0Diagram.parameter (s, t), x) =
      (boundedFlatCoefficientBassComparisonHomotopy P v).level n
        (s, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P b)) n
            (t, (boundedFlatPerfectPrespectrumMap (coefficientMap P u)).map n x)) := by
  rw [middle_simplex_original, prespectrumSimplexFamily_precomp, BassH0Diagram.native]
  rfl

variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)

/-- Actual composition of two independently varying original square diagrams. -/
def chartProduct := CommonReferenceProduct.simplex
  (CoefficientSquareFamilies.polynomialSource P u)
  (fun i ↦ (CoefficientSquareFamilies.polynomialNodes P u i).1)
  (fun i ↦ (CoefficientSquareFamilies.polynomialNodes P u i).2)
  (CoefficientSquareFamilies.chartSource P v α)
  (fun i ↦ (CoefficientSquareFamilies.chartNodes P v α i).1)
  (fun i ↦ (CoefficientSquareFamilies.chartNodes P v α i).2)

/-- The real realization-product parameter composes both whole families at every original level. -/
theorem chart_product_family (n : ℕ) (z w : StdSimplex ℝ (Fin 5))
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (chartProduct P u v α) n
      (SimplexGrid.parameter.{u + 1} 4 4 (z, w), x) =
      prespectrumSimplexFamily (CoefficientSquareFamilies.chartSimplex P v α) n
        (w, prespectrumSimplexFamily (CoefficientSquareFamilies.polynomialSimplex P u) n (z, x)) :=
  CommonReferenceProduct.prespectrum_comp _ _ _ _ _ _ n x z w

/-- Both scalar times are independent in the positive product piece. -/
def plusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 25)) :=
  ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 4 4
    (NativeSquareFiveSimplex.parameter z.2, NativeSquareFiveSimplex.parameter z.1), by fun_prop⟩

/-- The inverse piece retains the original reversal of the polynomial-square time. -/
def minusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 25)) :=
  ⟨fun z ↦ SimplexGrid.parameter.{u + 1} 4 4
    (NativeSquareFiveSimplex.parameter (unitInterval.symm z.2),
      NativeSquareFiveSimplex.parameter z.1), by fun_prop⟩

/-- Whole first span-cylinder segment after the independently moving positive v-square. -/
theorem plus_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (chartProduct P u v (underToLaurent R)) n
      (plusParameter.{u} (s, t), x) =
      (boundedFlatCoefficientPlusSquareHomotopy P v).level n
        (s, (boundedFlatCoefficientPolynomialSquareHomotopy P u).level n (t, x)) := by
  change prespectrumSimplexFamily (chartProduct P u v (underToLaurent R)) n
    (SimplexGrid.parameter 4 4 (_, _), x) = _
  rw [chart_product_family, CoefficientSquareFamilies.polynomial_native,
    CoefficientSquareFamilies.plus_native]

/-- Whole final span-cylinder segment, retaining its reverse polynomial and inverse-chart values. -/
theorem minus_native (n : ℕ) (s t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (chartProduct P u v (underToLaurentInvert R)) n
      (minusParameter.{u} (s, t), x) =
      (boundedFlatCoefficientMinusSquareHomotopy P v).level n
        (s, (boundedFlatCoefficientPolynomialSquareHomotopy P u).level n
          (unitInterval.symm t, x)) := by
  change prespectrumSimplexFamily (chartProduct P u v (underToLaurentInvert R)) n
    (SimplexGrid.parameter 4 4 (_, _), x) = _
  rw [chart_product_family, CoefficientSquareFamilies.polynomial_native,
    CoefficientSquareFamilies.minus_native]

end Quillen.PerfectComplexes.BassH1Components
