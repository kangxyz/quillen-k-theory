/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Quillen.Aglib.Algebra.Polynomial.Laurent.Flat
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Basic

/-!
# Flat coefficient maps of the original polynomial and Laurent charts

Flatness follows from the actual coefficient pushouts. The resulting scheme squares retain the
literal coefficient homomorphisms and both Laurent chart maps.
-/
@[expose] public section

open Quillen.PolynomialBaseChange

open CommRingCat.PolynomialLaurent

open Quillen

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PolynomialLaurent

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

instance flat_spec_polynomialMap [Flat (Spec.map f)] : Flat (Spec.map (polynomialMap f)) :=
  Flat.SpecMap_iff.mpr (polynomialMap_flat f (Flat.SpecMap_iff.mp inferInstance))

instance flat_spec_laurentMap [Flat (Spec.map f)] : Flat (Spec.map (laurentMap f)) :=
  Flat.SpecMap_iff.mpr (laurentMap_flat f (Flat.SpecMap_iff.mp inferInstance))

/-- The original polynomial projection square commutes under coefficient change. -/

lemma polynomialMap_projection :
    Spec.map (polynomialMap f) ≫ polynomialProjection R = polynomialProjection S ≫ Spec.map f := by
  simpa only [polynomialProjection, coefficient, ← Spec.map_comp] using
    congrArg Spec.map (polynomial_square f).symm

/-- The original Laurent projection square commutes under coefficient change. -/

lemma laurentMap_projection :
    Spec.map (laurentMap f) ≫ laurentProjection R = laurentProjection S ≫ Spec.map f := by
  simpa only [laurentProjection, laurentCoefficient, ← Spec.map_comp] using
    congrArg Spec.map (laurent_square f).symm

/-- Coefficient change commutes with the original positive Laurent chart. -/

lemma laurentMap_plus :
    Spec.map (laurentMap f) ≫ laurentPlus R = laurentPlus S ≫ Spec.map (polynomialMap f) := by
  simpa only [laurentPlus, ← Spec.map_comp] using
    congrArg Spec.map (toLaurent_naturality f).symm

/-- Coefficient change commutes with the original inverse-coordinate Laurent chart. -/

lemma laurentMap_minus :
    Spec.map (laurentMap f) ≫ laurentMinus R = laurentMinus S ≫ Spec.map (polynomialMap f) := by
  simpa only [laurentMinus, ← Spec.map_comp] using
    congrArg Spec.map (minus_naturality f).symm

end AlgebraicGeometry.Scheme.PolynomialLaurent
