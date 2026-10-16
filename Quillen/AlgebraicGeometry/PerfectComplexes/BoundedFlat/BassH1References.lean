/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.AlgebraicGeometry.BaseChange.Coefficients.Naturality
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassH1Components

/-! Actual geometric reference transports for all four prescribed H1 component families. -/
@[expose] public section

open Quillen.PerfectComplexes.BassReferenceMerge


open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH1References
open BassReferenceMerge
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Laurent composition and naturality give the literal first component's geometric total. -/
theorem first_total : coefficientMap P ((laurentUnderFunctor R).map v) ≫
    (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a) =
      laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u := by
  have h := BassH0Merge.total P u v
  rw [BassH0Merge.laurent_composite] at h
  simpa only [Category.assoc, laurentComposite] using h

/-- The middle cylinder uses the actual coefficient-u precomposition total. -/
theorem middle_total : (coefficientMap P ((laurentUnderFunctor R).map v) ≫
    laurentProjection P b) ≫ coefficientMap P u =
      laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u := by
  have h := AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
    (laurentUnderCoefficient R) v
  change coefficientMap P ((laurentUnderFunctor R).map v) ≫ laurentProjection P b =
    laurentProjection P c ≫ coefficientMap P v at h
  rw [h, Category.assoc]

/-- Both independent square products have the same total by the original projection equation. -/
theorem chart_total (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b) :
    (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b)) ≫
      (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a) =
        laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u := by
  have hp := AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
    (polynomialUnderCoefficient R) u
  change coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a =
    polynomialProjection P b ≫ coefficientMap P u at hp
  calc
    _ = (coefficientMap P ((laurentUnderFunctor R).map v) ≫
        (coefficientMap P (α.app b) ≫ polynomialProjection P b)) ≫ coefficientMap P u := by
      rw [hp]
      simp only [Category.assoc]
    _ = _ := by rw [hb]; exact middle_total P u v

/-- The original first family is reanchored by its actual normalized pullback comparison. -/
def firstIso : (BassOverlap.commonReference P u v).functor ≅
    (BassH1Components.firstSource P u v).functor :=
  smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (first_total P u v).symm) ≪≫
    boundedFlatNormalizedPullbackCompIso
      (coefficientMap P ((laurentUnderFunctor R).map v))
      (coefficientMap P ((laurentUnderFunctor R).map u) ≫ laurentProjection P a))

/-- The original middle family has the same reference via its actual normalization iso. -/
def middleIso : (BassOverlap.commonReference P u v).functor ≅
    (BassH1Components.middleSource P u v).functor :=
  smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (middle_total P u v).symm) ≪≫
    boundedFlatNormalizedPullbackCompIso
      (coefficientMap P ((laurentUnderFunctor R).map v) ≫ laurentProjection P b)
      (coefficientMap P u))

/-- Actual product-composition reference for a chart satisfying its original projection equation. -/
def chartIso (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b) :
    (BassOverlap.commonReference P u v).functor ≅
      (CoefficientSquareFamilies.polynomialSource P u ≫
        CoefficientSquareFamilies.chartSource P v α).functor :=
  smallIso (eqToIso (congrArg boundedFlatNormalizedPullback (chart_total P u v α hb).symm) ≪≫
    boundedFlatNormalizedPullbackCompIso
      (coefficientMap P ((laurentUnderFunctor R).map v) ≫ coefficientMap P (α.app b))
      (coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a))

/-- All full first-component nodes keep their original functors and canonical references. -/
def firstNodes : Fin 31 → BassOverlap.Node P u v :=
  ModelSimplex.reanchorNodes (firstIso P u v) (BassH1Components.firstNodes P u v)

/-- The middle H1 component nodes transported to the common Laurent reference via `middleIso`. -/
def middleNodes : Fin 31 → BassOverlap.Node P u v :=
  ModelSimplex.reanchorNodes (middleIso P u v) (BassH1Components.middleNodes P u v)

/-- The 25 product nodes of the polynomial-`u` and chart-`v` squares, with common Laurent
references. -/
def chartNodes (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b)
    (i : Fin 25) : BassOverlap.Node P u v :=
  ⟨CommonReferenceProduct.vertices
      (fun j ↦ (CoefficientSquareFamilies.polynomialNodes P u j).1)
      (fun j ↦ (CoefficientSquareFamilies.chartNodes P v α j).1) i,
    chartIso P u v α hb ≪≫ CommonReferenceProduct.references
      (CoefficientSquareFamilies.polynomialSource P u)
      (fun j ↦ (CoefficientSquareFamilies.polynomialNodes P u j).1)
      (fun j ↦ (CoefficientSquareFamilies.polynomialNodes P u j).2)
      (CoefficientSquareFamilies.chartSource P v α)
      (fun j ↦ (CoefficientSquareFamilies.chartNodes P v α j).1)
      (fun j ↦ (CoefficientSquareFamilies.chartNodes P v α j).2) i⟩

/-- Reanchoring retains the entire original first family, with no new scalar choices. -/
theorem first_original : ModelSimplex.ofIsos (BassOverlap.commonReference P u v)
    (fun i ↦ (firstNodes P u v i).1) (fun i ↦ (firstNodes P u v i).2) =
    BassH1Components.firstSimplex P u v :=
  ModelSimplex.ofIsos_change_reference (firstIso P u v) _ _

theorem middle_original : ModelSimplex.ofIsos (BassOverlap.commonReference P u v)
    (fun i ↦ (middleNodes P u v i).1) (fun i ↦ (middleNodes P u v i).2) =
    BassH1Components.middleSimplex P u v :=
  ModelSimplex.ofIsos_change_reference (middleIso P u v) _ _

/-- The whole independently varying product family is retained with its actual references. -/
theorem chart_original (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
    (hb : coefficientMap P (α.app b) ≫ polynomialProjection P b = laurentProjection P b) :
    ModelSimplex.ofIsos (BassOverlap.commonReference P u v)
      (fun i ↦ (chartNodes P u v α hb i).1) (fun i ↦ (chartNodes P u v α hb i).2) =
      BassH1Components.chartProduct P u v α :=
  ModelSimplex.ofIsos_change_reference (chartIso P u v α hb) _ _

end Quillen.PerfectComplexes.BassH1References
