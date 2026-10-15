/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.SectionBassPushoutStableEquivalence

/-!
# Actual Laurent-span stable preservation consumers

The strict actual Laurent evaluation square and its unchanged coefficient maps supply the span.
Three original stable corner maps imply stable equivalence of its existing spanMap, including
negative degrees. Its original C inclusion and full overlap cylinder remain literal.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen Quillen.PerfectComplexes Quillen.LoopPrespectrum
open scoped unitInterval
universe u
namespace QuillenTest.SectionBassPushoutStableEquivalence

open Quillen

/-- The actual Laurent evaluation square at the original finite stage. -/
def originalLaurentSquare (i : ℕ) (R : CommRingCat.{u}) :
    Arrow (Arrow LoopPrespectrum.{u + 1}) :=
  (boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.obj
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R)

/-- The actual coefficient map of the unchanged Laurent evaluation squares. -/
def originalLaurentSquareMap (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S) :
    originalLaurentSquare i R ⟶ originalLaurentSquare i S :=
  (boundedFlatAffineSectionBassDiagram i).mapArrow.mapArrow.map
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.map f)

/-- The actual Laurent span map preserves stable equivalences from original stable sides. -/
theorem actual_laurent_span_stable (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S)
    (ha : IsStableEquivalence (originalLaurentSquareMap i f).left.left)
    (hb : IsStableEquivalence (originalLaurentSquareMap i f).left.right)
    (hc : IsStableEquivalence (originalLaurentSquareMap i f).right.left) :
    IsStableEquivalence (StrictSquare.spanMap (originalLaurentSquareMap i f)) :=
  boundedFlatAffineSectionBass_pushoutMap_isStableEquivalence i i i i i i
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R).left.left
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R).left.right
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj R).right.left
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj S).left.left
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj S).left.right
    (CommRingCat.PolynomialLaurent.laurentSquareFunctor.obj S).right.left
    _ _ _ _ _ _ _ _ _ ha hb hc

/-- The same original Laurent-span map is invertible in every negative stable degree. -/
theorem actual_laurent_span_negative_iso (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S)
    (ha : IsStableEquivalence (originalLaurentSquareMap i f).left.left)
    (hb : IsStableEquivalence (originalLaurentSquareMap i f).left.right)
    (hc : IsStableEquivalence (originalLaurentSquareMap i f).right.left) (k : ℕ) :
    IsIso ((stableHomotopyFunctor (-(Int.ofNat k + 1))).map
      (StrictSquare.spanMap (originalLaurentSquareMap i f))) :=
  actual_laurent_span_stable i f ha hb hc _

/-- The original C inclusion and original coefficient side are retained exactly. -/
theorem actual_laurent_span_right_inclusion (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S) :
    HomotopyPushout.inr (originalLaurentSquare i R).left.hom (originalLaurentSquare i R).hom.left ≫
      StrictSquare.spanMap (originalLaurentSquareMap i f) =
        (originalLaurentSquareMap i f).right.left ≫ HomotopyPushout.inr
          (originalLaurentSquare i S).left.hom (originalLaurentSquare i S).hom.left := by
  apply Hom.ext
  funext n
  ext x
  rfl

/-- The whole overlap cylinder retains its independent time and original source coefficient map. -/
theorem actual_laurent_span_cylinder (i : ℕ) {R S : CommRingCat.{u}} (f : R ⟶ S)
    (n : ℕ) (t : unitInterval) (x : (originalLaurentSquare i R).left.left.space n) :
    (StrictSquare.spanMap (originalLaurentSquareMap i f)).map n
      (HomotopyPushout.cylinder (originalLaurentSquare i R).left.hom
        (originalLaurentSquare i R).hom.left n (t, x)) =
      HomotopyPushout.cylinder (originalLaurentSquare i S).left.hom
        (originalLaurentSquare i S).hom.left n
          (t, (originalLaurentSquareMap i f).left.left.map n x) := rfl

end QuillenTest.SectionBassPushoutStableEquivalence
