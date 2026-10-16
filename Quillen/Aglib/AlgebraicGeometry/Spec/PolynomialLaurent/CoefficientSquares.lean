/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Basic
public import Quillen.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Actual coefficient pullback squares for polynomial and Laurent spectra -/
@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CommRingCat.PolynomialLaurent
namespace AlgebraicGeometry.Scheme.ProjectiveLine
open PolynomialLaurent
variable {R S : CommRingCat.{u}} (f : R ⟶ S)

/-- The original polynomial coefficient square is cartesian. -/
lemma polynomialProjection_isPullback :
    IsPullback (polynomialProjection S) (Spec.map (polynomialMap f))
      (Spec.map f) (polynomialProjection R) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (polynomial_isPushout f)

/-- The original Laurent coefficient square is cartesian. -/
lemma laurentProjection_isPullback :
    IsPullback (laurentProjection S) (Spec.map (laurentMap f))
      (Spec.map f) (laurentProjection R) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (laurent_isPushout f)

/-- Coefficient change gives the actual cartesian positive-overlap square. -/
lemma laurentPlus_isPullback :
    IsPullback (laurentPlus S) (Spec.map (laurentMap f))
      (Spec.map (polynomialMap f)) (laurentPlus R) := by
  apply IsPullback.of_right (h₁₂ := polynomialProjection S)
    (h₂₂ := polynomialProjection R) _ (laurentMap_plus f).symm
    (polynomialProjection_isPullback f)
  simpa only [laurentPlus_projection] using laurentProjection_isPullback f

/-- Coefficient change gives the actual cartesian inverse-coordinate overlap square. -/
lemma laurentMinus_isPullback :
    IsPullback (laurentMinus S) (Spec.map (laurentMap f))
      (Spec.map (polynomialMap f)) (laurentMinus R) := by
  apply IsPullback.of_right (h₁₂ := polynomialProjection S)
    (h₂₂ := polynomialProjection R) _ (laurentMap_minus f).symm
    (polynomialProjection_isPullback f)
  simpa only [laurentMinus_projection] using laurentProjection_isPullback f

end AlgebraicGeometry.Scheme.ProjectiveLine
