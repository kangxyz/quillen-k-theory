/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSecondCoefficientProjection

/-! Exact original projection routes before parameter looping, for summand-wise descent. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open scoped Topology unitInterval
universe u v
namespace Quillen.PerfectComplexes.CoefficientBassLaurentProjectionRoutes
variable {R : CommRingCat.{u}} (P : Over (Spec R))

/-- The actual Laurent-fiber coefficient map, without a base-image restriction. -/
def laurentMap {a b : Under R} (u : a ⟶ b) :=
  boundedFlatPerfectPrespectrumMap (coefficientMap P ((laurentUnderFunctor R).map u))

/-- The original positive-chart Laurent composition homotopy with its actual source equality
cast. -/
def plusComposition (a : Under R) :=
  (boundedFlatCoefficientLaurentCompositionHomotopy P ((polynomialUnderCoefficient R).app a)
    ((underToLaurent R).app a)).cast
      (congrArg (laurentMap P)
        (polynomialUnderCoefficient_toLaurent R a)) rfl

/-- The original inverse-chart Laurent composition homotopy with its actual source equality cast. -/
def minusComposition (a : Under R) :=
  (boundedFlatCoefficientLaurentCompositionHomotopy P ((polynomialUnderCoefficient R).app a)
    ((underToLaurentInvert R).app a)).cast
      (congrArg (laurentMap P)
        (polynomialUnderCoefficient_toLaurentInvert R a)) rfl

variable {a b : Under R} (u : a ⟶ b)

/-- The selected first-step composition tracks lift the literal naturality equation.
The reversed first track and the forward second track retain their original half clocks. -/
def naturalitySquare {M N : Under R ⥤ Under R} (α : M ⟶ N) :
    Homotopy
      (laurentMap P (α.app a) ≫
        laurentMap P (N.map u))
      (laurentMap P (M.map u) ≫
        laurentMap P (α.app b)) :=
  (boundedFlatCoefficientLaurentCompositionHomotopy P (α.app a) (N.map u)).symm.trans
    ((boundedFlatCoefficientLaurentCompositionHomotopy P (M.map u) (α.app b)).cast
      (congrArg (laurentMap P) (α.naturality u)) rfl)

/-- The actual polynomial leg square at the first raw stage. -/
def polynomialSquare := naturalitySquare P u (polynomialUnderCoefficient R)

/-- The positive Laurent chart square at the first raw stage. -/
def plusSquare := naturalitySquare P u (underToLaurent R)

/-- The inverse Laurent chart has its own unchanged coefficient square. -/
def minusSquare := naturalitySquare P u (underToLaurentInvert R)

/-- Both chart pastings use this same literal Laurent-projection square. -/
def laurentSquare := naturalitySquare P u (laurentUnderCoefficient R)

/-- The polynomial span map exists before the missing Laurent comparison is filled. -/
def spanMap := HomotopyPushout.mapOfHomotopies
  (laurentMap P ((polynomialUnderCoefficient R).app a))
  (laurentMap P ((polynomialUnderCoefficient R).app a))
  (laurentMap P ((polynomialUnderCoefficient R).app b))
  (laurentMap P ((polynomialUnderCoefficient R).app b))
  (laurentMap P u)
  (laurentMap P ((polynomialUnderFunctor R).map u))
  (laurentMap P ((polynomialUnderFunctor R).map u))
  (polynomialSquare P u) (polynomialSquare P u)

/-- The positive route first crosses its chart square, then the polynomial square. -/
def plusLeft :=
  ((Homotopy.precomp
    (laurentMap P ((polynomialUnderCoefficient R).app a))
    (plusSquare P u)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((polynomialSquare P u).postcomp
      (laurentMap P ((underToLaurent R).app b)))

/-- The positive comparison retains the fixed second-object chart tracks and their casts. -/
def plusRight :=
  ((plusComposition P a).postcomp
    (laurentMap P ((laurentUnderFunctor R).map u))).symm.trans
    ((laurentSquare P u).trans
      ((Homotopy.precomp (laurentMap P u)
        (plusComposition P b)).cast
          rfl (Category.assoc _ _ _).symm))

/-- The inverse route uses the distinct inverse chart square, with the same polynomial leg. -/
def minusLeft :=
  ((Homotopy.precomp
    (laurentMap P ((polynomialUnderCoefficient R).app a))
    (minusSquare P u)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((polynomialSquare P u).postcomp
      (laurentMap P ((underToLaurentInvert R).app b)))

/-- The inverse comparison retains the original fixed inverse composition and common square. -/
def minusRight :=
  ((minusComposition P a).postcomp
    (laurentMap P ((laurentUnderFunctor R).map u))).symm.trans
    ((laurentSquare P u).trans
      ((Homotopy.precomp (laurentMap P u)
        (minusComposition P b)).cast
          rfl (Category.assoc _ _ _).symm))

/-- Every original cone composition restricts to the unchanged Laurent track. -/
theorem composition_inclusion {c : Under R} (v : b ⟶ c) (n : ℕ) (r : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    (BassMWhole.coneComposition P u v).level n
      (r, (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n x) =
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P c)).map n
      ((boundedFlatCoefficientLaurentCompositionHomotopy P u v).level n (r, x)) :=
  BassMWhole.cone_inclusion P u v n r x

/-- Actual cone maps preserve the entire Laurent summand. -/
theorem map_inclusion (n : ℕ)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientBassConeMap P u).map n
      ((mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P a)).map n x) =
    (mappingConeInclusion (boundedFlatCoefficientBassSquareComparison P b)).map n
      ((laurentMap P u).map n x) := by
  exact congrArg (fun k ↦ k.map n x) (boundedFlatCoefficientBassConeMap_inclusion P u)

end Quillen.PerfectComplexes.CoefficientBassLaurentProjectionRoutes
