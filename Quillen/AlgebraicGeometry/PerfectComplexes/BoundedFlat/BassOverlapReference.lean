/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceWhiskering
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassChartScalarFaces

/-! The two whole chart diagrams on the actual polynomial overlap have one geometric reference. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes.BassOverlap
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The exact model morphism inducing the original polynomial-projection prespectrum map. -/
def projectionMap : modelOf (boundedFlatPerfectWaldhausen (space (op P, a))) ⟶
    modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a))) :=
  modelMap _ _ (boundedFlatNormalizedPullback_exact (polynomialProjection P a))
    (boundedFlatNormalizedPullback_obj_zero _)

theorem projectionMap_prespectrum : prespectrumMap (projectionMap P (a := a)) =
    boundedFlatPerfectPrespectrumMap (polynomialProjection P a) := rfl

variable (α : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)

/-- The actual reference of the chart's already accepted merged 17-simplex. -/
def chartReference := NormalizedTripleSimplex.sourceMap
  (coefficientMap P (α.app c))
  (coefficientMap P ((polynomialUnderFunctor R).map v))
  (coefficientMap P ((polynomialUnderFunctor R).map u))

/-- The overlap reference uses only the common Laurent projection and the two coefficient maps. -/
def commonReference : modelOf (boundedFlatPerfectWaldhausen (space (op P, a))) ⟶
    modelOf (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c))) :=
  modelMap _ _ (boundedFlatNormalizedPullback_exact
    (laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u))
    (boundedFlatNormalizedPullback_obj_zero _)

/-- Polynomial naturality and the actual chart projection equation identify the geometric total. -/
theorem chart_total
    (hα : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    (coefficientMap P (α.app c) ≫
      coefficientMap P ((polynomialUnderFunctor R).map v) ≫
      coefficientMap P ((polynomialUnderFunctor R).map u)) ≫ polynomialProjection P a =
      laurentProjection P c ≫ coefficientMap P v ≫ coefficientMap P u := by
  have hu := coefficientTransformation_naturality P (polynomialUnderCoefficient R) u
  have hv := coefficientTransformation_naturality P (polynomialUnderCoefficient R) v
  change coefficientMap P ((polynomialUnderFunctor R).map u) ≫ polynomialProjection P a =
    polynomialProjection P b ≫ coefficientMap P u at hu
  change coefficientMap P ((polynomialUnderFunctor R).map v) ≫ polynomialProjection P b =
    polynomialProjection P c ≫ coefficientMap P v at hv
  simp only [Category.assoc]
  rw [hu, ← Category.assoc _ _ (coefficientMap P u), hv]
  simp only [Category.assoc]
  rw [← Category.assoc (coefficientMap P (α.app c)) (polynomialProjection P c), hα]

/-- An actual normalized pullback composition iso, after the literal geometric total equality. -/
def commonToChartReference
    (hα : coefficientMap P (α.app c) ≫ polynomialProjection P c = laurentProjection P c) :
    (commonReference P u v).functor ≅
      (projectionMap P (a := a) ≫ chartReference P u v α).functor :=
  isoWhiskerLeft AsSmall.down (isoWhiskerRight
    (eqToIso (congrArg boundedFlatNormalizedPullback (chart_total P u v α hα).symm) ≪≫
      boundedFlatNormalizedPullbackCompIso
        (coefficientMap P (α.app c) ≫
          coefficientMap P ((polynomialUnderFunctor R).map v) ≫
          coefficientMap P ((polynomialUnderFunctor R).map u))
        (polynomialProjection P a)) AsSmall.up)

/-- The positive chart supplies its original geometric projection equation. -/
def plusReference := commonToChartReference P u v (underToLaurent R)
  (laurentPlus_projection P c)

/-- The negative chart supplies its distinct original geometric projection equation. -/
def minusReference := commonToChartReference P u v (underToLaurentInvert R)
  (laurentMinus_projection P c)

end Quillen.PerfectComplexes.BassOverlap
