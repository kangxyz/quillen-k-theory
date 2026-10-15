/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Coefficients.Naturality
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassPrimitiveSupport

/-! Canonical common-reference transport of the complete original H0 diagram. -/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassH0Merge
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The original Laurent coefficient composite is the actual composite scheme map. -/
theorem laurent_composite : coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)) =
    BassReferenceMerge.laurentComposite P u v := by
  rw [Functor.map_comp, coefficientMap_comp]

/-- The original polynomial coefficient composite has the analogous literal scheme equality. -/
theorem polynomial_composite : coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v)) =
    coefficientMap P ((polynomialUnderFunctor R).map v) ≫
      coefficientMap P ((polynomialUnderFunctor R).map u) := by
  rw [Functor.map_comp, coefficientMap_comp]

/-- Native Laurent naturality identifies the H0 source with the old common geometric total. -/
theorem total : coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)) ≫
    laurentProjection P a =
      laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u := by
  have h := AlgebraicGeometry.Scheme.BaseChange.Coefficients.coefficientMap_naturality P
    (laurentUnderCoefficient R) (u ≫ v)
  change coefficientMap P ((laurentUnderFunctor R).map (u ≫ v)) ≫ laurentProjection P a =
    laurentProjection P c ≫ coefficientMap P (u ≫ v) at h
  rw [coefficientMap_comp] at h
  exact h

/-- The anchored source equality is induced only by the actual geometric total equation. -/
theorem reference_eq : (BassOverlap.commonReference P u v).functor =
    (BassH0Diagram.reference P (u ≫ v)).functor :=
  congrArg (fun F ↦ AsSmall.down ⋙ F ⋙ AsSmall.up)
    (congrArg boundedFlatNormalizedPullback (total P u v).symm)

/-- Every old H0 node retains its actual functor and reference after canonical transport. -/
def nodes : Fin 31 → BassOverlap.Node P u v :=
  ModelSimplex.reanchorNodes (F₀ := BassOverlap.commonReference P u v)
    (F₁ := BassH0Diagram.reference P (u ≫ v)) (eqToIso (reference_eq P u v))
    (BassH0Diagram.nodes P (u ≫ v))

/-- The original H0 simplex reanchored at the common Laurent reference via `reference_eq`. -/
def simplex := ModelSimplex.reanchorSimplex
  (F₀ := BassOverlap.commonReference P u v) (F₁ := BassH0Diagram.reference P (u ≫ v))
  (eqToIso (reference_eq P u v)) (BassH0Diagram.nodes P (u ≫ v))

/-- This reanchoring preserves the entire original H0 simplex, hence every existing native value. -/
theorem simplex_original : simplex P u v = BassH0Diagram.simplex P (u ≫ v) :=
  ModelSimplex.reanchorSimplex_eq (eqToIso (reference_eq P u v))
    (BassH0Diagram.nodes P (u ≫ v))

end Quillen.PerfectComplexes.BassH0Merge
