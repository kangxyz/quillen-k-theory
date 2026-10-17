/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSecondStep

/-! Exact coefficient squares and projection-pasting targets for the fixed raw second object.
The squares use the chosen whole first-step composition tracks. The two relative-pasting
abbreviations below name the remaining mathematical obligations; no fillers are assumed.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open Quillen.LoopPrespectrum CommRingCat.PolynomialLaurent
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSecondCoefficientProjection
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b : Under R} (u : a ⟶ b)

/-- The selected first-step composition tracks lift the literal naturality equation.
The reversed first track and the forward second track retain their original half clocks. -/
def naturalitySquare {M N : Under R ⥤ Under R} (α : M ⟶ N) :
    Homotopy
      (boundedFlatCoefficientBassStepMap P (α.app a) ≫
        boundedFlatCoefficientBassStepMap P (N.map u))
      (boundedFlatCoefficientBassStepMap P (M.map u) ≫
        boundedFlatCoefficientBassStepMap P (α.app b)) :=
  (BassMWhole.stepComposition P (α.app a) (N.map u)).symm.trans
    ((BassMWhole.stepComposition P (M.map u) (α.app b)).cast
      (congrArg (boundedFlatCoefficientBassStepMap P) (α.naturality u)) rfl)

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
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app b))
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app b))
  (boundedFlatCoefficientBassStepMap P u)
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderFunctor R).map u))
  (boundedFlatCoefficientBassStepMap P ((polynomialUnderFunctor R).map u))
  (polynomialSquare P u) (polynomialSquare P u)

/-- The positive route first crosses its chart square, then the polynomial square. -/
def plusLeft :=
  ((Homotopy.precomp
    (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
    (plusSquare P u)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((polynomialSquare P u).postcomp
      (boundedFlatCoefficientBassStepMap P ((underToLaurent R).app b)))

/-- The positive comparison retains the fixed second-object chart tracks and their casts. -/
def plusRight :=
  ((boundedFlatCoefficientBassSecondPlusHomotopy P a).postcomp
    (boundedFlatCoefficientBassStepMap P ((laurentUnderFunctor R).map u))).symm.trans
    ((laurentSquare P u).trans
      ((Homotopy.precomp (boundedFlatCoefficientBassStepMap P u)
        (boundedFlatCoefficientBassSecondPlusHomotopy P b)).cast
          rfl (Category.assoc _ _ _).symm))

/-- The inverse route uses the distinct inverse chart square, with the same polynomial leg. -/
def minusLeft :=
  ((Homotopy.precomp
    (boundedFlatCoefficientBassStepMap P ((polynomialUnderCoefficient R).app a))
    (minusSquare P u)).cast
      (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm).trans
    ((polynomialSquare P u).postcomp
      (boundedFlatCoefficientBassStepMap P ((underToLaurentInvert R).app b)))

/-- The inverse comparison retains the original fixed inverse composition and common square. -/
def minusRight :=
  ((boundedFlatCoefficientBassSecondMinusHomotopy P a).postcomp
    (boundedFlatCoefficientBassStepMap P ((laurentUnderFunctor R).map u))).symm.trans
    ((laurentSquare P u).trans
      ((Homotopy.precomp (boundedFlatCoefficientBassStepMap P u)
        (boundedFlatCoefficientBassSecondMinusHomotopy P b)).cast
          rfl (Category.assoc _ _ _).symm))

/-- Exact missing positive full-route filler for the second coefficient map. -/
abbrev PlusPasting := (plusLeft P u).RelHomotopy (plusRight P u)

/-- Exact missing inverse-chart full-route filler for the second coefficient map. -/
abbrev MinusPasting := (minusLeft P u).RelHomotopy (minusRight P u)

/-- The span map retains its literal positive chart coefficient map. -/
theorem spanMap_inl :
    HomotopyPushout.inl _ _ ≫ spanMap P u =
      boundedFlatCoefficientBassStepMap P ((polynomialUnderFunctor R).map u) ≫
        HomotopyPushout.inl _ _ :=
  HomotopyPushout.inl_mapOfHomotopies _ _ _ _ _ _ _ _ _

/-- The span map retains the distinct right chart with the same coefficient arrow. -/
theorem spanMap_inr :
    HomotopyPushout.inr _ _ ≫ spanMap P u =
      boundedFlatCoefficientBassStepMap P ((polynomialUnderFunctor R).map u) ≫
        HomotopyPushout.inr _ _ :=
  HomotopyPushout.inr_mapOfHomotopies _ _ _ _ _ _ _ _ _

end Quillen.PerfectComplexes.CoefficientBassSecondCoefficientProjection
