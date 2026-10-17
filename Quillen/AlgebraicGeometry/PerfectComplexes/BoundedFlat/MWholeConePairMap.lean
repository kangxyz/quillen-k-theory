/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MWholeConePairProjection
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialPairCone
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeConeEvaluation
public import Quillen.Topology.DoubleMappingCylinder.Invariance

/-! Each original polynomial pair sheet maps into its actual ordinary chart cone cell. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMWholeConeCarrier.PairProjection
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open BassProjectionPath.WholeReference
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
local notation "E" => inputReference P p q
local notation "F" => CoefficientBassRaw1PolynomialPausedChart.polynomialReference P p q
local notation "Jd" => normalizedMap (polynomialProjection P c)
local notation "H" => BassProjectionPath.WholeReference.reference P c E
local notation "βd" => FourEdge.beta P c E

variable (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hd : coefficientMap P (β.app c) ≫ polynomialProjection P c = laurentProjection P c)
local notation "J" => BassMWholeNerve.coefficientModel P (β.app c)
local notation "G" => F ≫ J

variable (v : parameterSSet (inputReference P p q ≫ normalizedMap (polynomialProjection P c)) ⟶
    FourEdgeTree.simplicial (inputReference P p q) (normalizedMap (polynomialProjection P c)))
  (hv : v ≫ FourEdge.beta P c (inputReference P p q) =
    FourEdge.chartMap P c (inputReference P p q) β hd)

/-- A prescribed chart vertex, after the full source-polynomial reference transport. -/
def vertex : |parameterSSet F| ⟶ FourEdgeTree.space E Jd :=
  TopCat.ofHom ((SSet.toTop.map v).hom.comp (polynomial P p q))

include hv in
/-- The exact whole-reference attachment square supplies the actual quotient map. -/
theorem attachment_square :
    SSet.toTop.map (attaching F J G (Iso.refl _)) ≫ TopCat.ofHom (laurent P p q β hd) =
      vertex P p q v ≫ SSet.toTop.map βd := by
  ext y
  change laurent P p q β hd (mapParameter (attachPostcompNode F J G (Iso.refl _)) y) =
    SSet.toTop.map βd (SSet.toTop.map v (polynomial P p q y))
  rw [← FourEdgeTree.realized_comp, hv]
  exact attachment_parameter P p q β hd y

/-- Source projection sends the one original sheet tip to the one original ordinary tip. -/
theorem erase_square :
    SSet.toTop.map (erase F) ≫ 𝟙 _ = vertex P p q v ≫
      SSet.toTop.map (SSet.stdSimplex.isTerminalObj₀.from (FourEdgeTree.simplicial E Jd)) := by
  ext y
  exact Subsingleton.elim _ _

/-- This is the existing map of displayed double cylinders; its height coordinate is unchanged. -/
def map : C(CoefficientBassRaw1PolynomialPairCone.carrier P β p q,
    FourEdge.scalarCone P c E) :=
  (DoubleCylinder.map (first_isPushout F J G (Iso.refl _))
    (DoubleCylinder.realized_isPushout βd (SSet.stdSimplex.isTerminalObj₀.from _))
    (vertex P p q v) (TopCat.ofHom (laurent P p q β hd)) (𝟙 _)
    (attachment_square P p q β hd v hv) (erase_square P p q v)).hom

/-- The full Laurent baseline is transported with its proved original anchor. -/
theorem map_laurent (y : |parameterSSet G|) :
    map P p q β hd v hv (SSet.toTop.map (left₀ F J G (Iso.refl _)) y) =
      FourEdgeTree.laurentInclusion E Jd H βd (laurent P p q β hd y) := by
  have h₀ := congrArg (map P p q β hd v hv)
    (FourEdgeTree.SetDescent.eval_realized_left
      (attaching F J G (Iso.refl _)) (erase F) y)
  have h₁ := DoubleCylinder.map_left (first_isPushout F J G (Iso.refl _))
    (DoubleCylinder.realized_isPushout βd (SSet.stdSimplex.isTerminalObj₀.from _))
    (vertex P p q v) (TopCat.ofHom (laurent P p q β hd)) (𝟙 _)
    (attachment_square P p q β hd v hv) (erase_square P p q v) y
  exact h₀.trans (h₁.trans (FourEdgeTree.SetDescent.eval_realized_left
    βd (SSet.stdSimplex.isTerminalObj₀.from _) (laurent P p q β hd y)).symm)

/-- The original terminal point maps to the same ordinary cone tip. -/
theorem map_tip :
    map P p q β hd v hv
      (SSet.toTop.map (right₀ F J G (Iso.refl _)) (default : |tipSSet.{u+1}|)) =
      FourEdgeTree.tip E Jd H βd := by
  have h₀ := congrArg (map P p q β hd v hv)
    (FourEdgeTree.SetDescent.eval_realized_right
      (attaching F J G (Iso.refl _)) (erase F) (default : |tipSSet.{u+1}|))
  have h₁ := DoubleCylinder.map_right (first_isPushout F J G (Iso.refl _))
    (DoubleCylinder.realized_isPushout βd (SSet.stdSimplex.isTerminalObj₀.from _))
    (vertex P p q v) (TopCat.ofHom (laurent P p q β hd)) (𝟙 _)
    (attachment_square P p q β hd v hv) (erase_square P p q v) default
  exact h₀.trans (h₁.trans (FourEdgeTree.SetDescent.eval_realized_right
    βd (SSet.stdSimplex.isTerminalObj₀.from _) default).symm)

/-- Every source cylinder keeps its independent literal original height. -/
theorem map_cylinder (y : |parameterSSet F|) (t : I) :
    map P p q β hd v hv
      (DoubleCylinder.realizedCylinder (attaching F J G (Iso.refl _)) (erase F)
        (y, ULift.up t)) =
      FourEdgeTree.cylinder E Jd H βd (vertex P p q v y, t) :=
  DoubleCylinder.map_cylinder_apply _ _ _ _ _ _ _ _ _

/-- The positive chart uses its entire original polynomial vertex. -/
def plus : C(CoefficientBassRaw1PolynomialPairCone.carrier P (underToLaurent R) p q,
    FourEdge.scalarCone P c E) :=
  map P p q (underToLaurent R) (laurentPlus_projection P c)
    (FourEdgeTree.plusVertex E Jd) (FourEdge.beta_plus P c E)

/-- The inverse chart uses its own polynomial vertex and the same ordinary tip. -/
def minus : C(CoefficientBassRaw1PolynomialPairCone.carrier P (underToLaurentInvert R) p q,
    FourEdge.scalarCone P c E) :=
  map P p q (underToLaurentInvert R) (laurentMinus_projection P c)
    (FourEdgeTree.minusVertex E Jd) (FourEdge.beta_minus P c E)

/-- The entire positive original Q face maps to the frozen M face, with both old times. -/
theorem plus_chartSquare (r s : I) :
    plus P p q (CoefficientBassRaw1PolynomialPairCone.chartSquare P
      (underToLaurent R) p q (r, s)) = cube P p q (r, (s, 0)) := by
  unfold plus
  dsimp only [CoefficientBassRaw1PolynomialPairCone.chartSquare, ContinuousMap.comp_apply]
  rw [map_laurent, plus_chart_face]
  rfl

/-- The inverse original Q face uses its own chart and the same unchanged outer height. -/
theorem minus_chartSquare (r s : I) :
    minus P p q (CoefficientBassRaw1PolynomialPairCone.chartSquare P
      (underToLaurentInvert R) p q (r, s)) = cube P p q (r, (s, 1)) := by
  unfold minus
  dsimp only [CoefficientBassRaw1PolynomialPairCone.chartSquare, ContinuousMap.comp_apply]
  rw [map_laurent, minus_chart_face]
  rfl

end Quillen.PerfectComplexes.BassMWholeConeCarrier.PairProjection
