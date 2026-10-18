/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSectionChangeIndexLaws

/-! # Actual geometric restriction regressions -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.Waldhausen.IteratedS Quillen.KTheory.Bass Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace QuillenTest.GlobalSectionChangeIndex

/-- The comparison is an actual natural transformation of original S-prespectra. -/
def restrictionPrespectrum (R : CommRingCat.{u}) :
    (AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R ⋙ globalModel) ⋙
      prespectrumFunctor ⟶ boundedFlatCoefficientSectionPrespectrumFunctor R :=
  Functor.whiskerRight (coefficientRestriction R) prespectrumFunctor

example (R : CommRingCat.{u}) {i j : Index R} (f : i ⟶ j) :
    globalModel.map ((AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).map f) ≫
      (coefficientRestriction R).app j =
    (coefficientRestriction R).app i ≫ boundedFlatCoefficientSectionModelMap f :=
  (coefficientRestriction R).naturality f

example (R : CommRingCat.{u}) (i : Index R) :
    ((coefficientRestriction R).app i).functor.obj
      (globalModel.obj
        ((AlgebraicGeometry.Scheme.BaseChange.Coefficients.functor R).obj i)).waldhausen.zero =
      boundedFlatCoefficientSectionZero i :=
  ((coefficientRestriction R).app i).zero

example (R : CommRingCat.{u}) (Q : Index R ⥤ Arrow (Arrow (Index R)))
    (n : ℕ) (i : Index R) :
    IsStableEquivalence (((strictDiagramIterate Q n).map (restrictionPrespectrum R)).app i) :=
  coefficientRestriction_iterate_isStableEquivalence R Q n i

end QuillenTest.GlobalSectionChangeIndex
