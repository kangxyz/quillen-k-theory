/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialCapLowerFaces

/-!
# The two original total-pair caps in a polynomial triple sheet

Full source-reference normalization places the corrected caps for `(p ≫ q, w)` and
`(p, q ≫ w)` in the original triple sheet. Every transport is induced by the polynomial
or Laurent functor's composition equality, retaining the original cap and both clocks.
The lower faces are identified on complete reference nodes before realization.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite Convexity
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.SimplexParameters
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialRadialCaps
open CommonReferenceNerve BassH0Merge BassReferenceMerge
open CoefficientBassRaw1PolynomialTripleAnchor CoefficientBassRaw1PolynomialTripleLowerFaces

/-- Equality of the whole polynomial pair reference, retaining the original functor composition. -/
theorem pairPolynomialEq {R : CommRingCat.{u}} (P : Over (Spec R))
    {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c) :
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q).functor =
      (BassMWholeNerve.coefficientModel P ((polynomialUnderFunctor R).map (p ≫ q))).functor := by
  change (normalizedMap (polynomialArrow P q ≫ polynomialArrow P p)).functor =
    (normalizedMap (coefficientMap P ((polynomialUnderFunctor R).map (p ≫ q)))).functor
  simp only [Functor.map_comp, coefficientMap_comp]

/-- The complete polynomial pair normalization is the literal equality isomorphism. -/
def pairPolynomialIso {R : CommRingCat.{u}} (P : Over (Spec R))
    {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c) :=
  eqToIso (pairPolynomialEq P p q)

/-- The two radial binary rows use precisely their original split-triple vertices. -/
def leftIndex : Fin 3 → Fin 8 := ![0, 1, 2]
/-- The right radial face indices `0`, `4`, and `5` in the eight-node triple reference. -/
def rightIndex : Fin 3 → Fin 8 := ![0, 4, 5]

section Triple
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)

/-- The left radial total equality is polynomial functor composition. -/
theorem leftPolynomialEq : polynomialTotal P p q w =
    polynomialArrow P w ≫ polynomialArrow P (p ≫ q) := by
  simp only [polynomialArrow, Functor.map_comp, coefficientMap_comp]

/-- The right radial total equality additionally retains the original association. -/
theorem rightPolynomialEq : polynomialTotal P p q w =
    polynomialArrow P (q ≫ w) ≫ polynomialArrow P p := by
  simp only [polynomialArrow, Functor.map_comp, coefficientMap_comp]
  exact (Category.assoc _ _ _).symm

theorem leftLaurentEq : laurentTotal P p q w =
    laurentArrow P w ≫ laurentArrow P (p ≫ q) := by
  simp only [laurentArrow, Functor.map_comp, coefficientMap_comp]

theorem rightLaurentEq : laurentTotal P p q w =
    laurentArrow P (q ≫ w) ≫ laurentArrow P p := by
  simp only [laurentArrow, Functor.map_comp, coefficientMap_comp]
  exact (Category.assoc _ _ _).symm

/-- Both original polynomial references are retained by equality isomorphisms. -/
def leftPolynomialIso := eqToIso
  (congrArg (fun k ↦ (normalizedMap k).functor) (leftPolynomialEq P p q w))
/-- The normalized reference isomorphism for the right radial polynomial decomposition. -/
def rightPolynomialIso := eqToIso
  (congrArg (fun k ↦ (normalizedMap k).functor) (rightPolynomialEq P p q w))
/-- The normalized reference isomorphism for the left radial Laurent decomposition. -/
def leftLaurentIso := eqToIso
  (congrArg (fun k ↦ (normalizedMap k).functor) (leftLaurentEq P p q w))
/-- The normalized reference isomorphism for the right radial Laurent decomposition. -/
def rightLaurentIso := eqToIso
  (congrArg (fun k ↦ (normalizedMap k).functor) (rightLaurentEq P p q w))

/-- Full source-reference normalization of the original left radial pair sheet. -/
def leftMap : C(CoefficientBassRaw1PolynomialPairCone.carrier P β (p ≫ q) w,
    CoefficientBassRaw1PolynomialPostcomp.carrier P p q w β) :=
  CoefficientBassPolynomialSheetNormalization.map
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P (p ≫ q) w)
    (polynomialReference P p q w) (normalizedMap (chart P β d))
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β (p ≫ q) w)
    (Iso.refl _) (leftPolynomialIso P p q w)

/-- Full source-reference normalization of the original right radial pair sheet. -/
def rightMap : C(CoefficientBassRaw1PolynomialPairCone.carrier P β p (q ≫ w),
    CoefficientBassRaw1PolynomialPostcomp.carrier P p q w β) :=
  CoefficientBassPolynomialSheetNormalization.map
    (CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p (q ≫ w))
    (polynomialReference P p q w) (normalizedMap (chart P β d))
    (CoefficientBassRaw1PolynomialPausedChart.sheetReference P β p (q ≫ w))
    (Iso.refl _) (rightPolynomialIso P p q w)

/-- The corrected left radial cap keeps its original two parameters. -/
def left : C(I × I, CoefficientBassRaw1PolynomialPostcomp.carrier P p q w β) :=
  (leftMap P β p q w).comp (CoefficientBassRaw1PolynomialPairCone.corrected P β (p ≫ q) w)

/-- The corrected right radial cap keeps its original two parameters. -/
def right : C(I × I, CoefficientBassRaw1PolynomialPostcomp.carrier P p q w β) :=
  (rightMap P β p q w).comp (CoefficientBassRaw1PolynomialPairCone.corrected P β p (q ≫ w))


end Triple
end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialRadialCaps
