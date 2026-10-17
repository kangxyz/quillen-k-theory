/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassRaw1PolynomialSourceProjection
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeConeEvaluation
public import Quillen.Topology.DoubleMappingCylinder.Invariance

/-! Each original polynomial triple sheet maps into its actual ordinary chart cone cell. -/
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
namespace Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialOrdinaryMap
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
open BassProjectionPath.WholeReference CoefficientBassRaw1PolynomialSourceProjection
variable {R : CommRingCat.{u}} (P : Over (Spec R))
  {a b c d : Under R} (p : a ⟶ b) (q : b ⟶ c) (w : c ⟶ d)
local notation "E" => input P p q w
local notation "F" => polynomial P p q w
local notation "Jd" => targetProjection P (d := d)
local notation "H" => BassProjectionPath.WholeReference.reference P d E
local notation "βd" => FourEdge.beta P d E

variable (β : polynomialUnderFunctor R ⟶ laurentUnderFunctor R)
  (hd : coefficientMap P (β.app d) ≫ polynomialProjection P d = laurentProjection P d)
local notation "J" => BassMWholeNerve.coefficientModel P (β.app d)
local notation "G" => F ≫ J

/-- The whole source-domain projection is followed by the complete Laurent reference map. -/
def laurent : C(|parameterSSet G|, |parameterSSet H|) :=
  mapParameter (laurentNode P p q w β hd)

/-- The polynomial node remains in its genuine target polynomial nerve. -/
def polynomial : C(|parameterSSet F|, |parameterSSet (E ≫ Jd)|) :=
  mapParameter (polynomialNode P p q w)

variable (v : parameterSSet (input P p q w ≫ targetProjection P (d := d)) ⟶
    FourEdgeTree.simplicial (input P p q w) (targetProjection P (d := d)))
  (hv : v ≫ FourEdge.beta P d (input P p q w) =
    FourEdge.chartMap P d (input P p q w) β hd)

/-- A prescribed chart vertex, after the full source-polynomial reference transport. -/
def vertex : |parameterSSet F| ⟶ FourEdgeTree.space E Jd :=
  TopCat.ofHom ((SSet.toTop.map v).hom.comp (polynomial P p q w))

include hv in
/-- The exact whole-reference attachment square supplies the actual quotient map. -/
theorem attachment_square :
    SSet.toTop.map (attaching F J G (Iso.refl _)) ≫ TopCat.ofHom (laurent P p q w β hd) =
      vertex P p q w v ≫ SSet.toTop.map βd := by
  ext y
  change laurent P p q w β hd (mapParameter (attachPostcompNode F J G (Iso.refl _)) y) =
    SSet.toTop.map βd (SSet.toTop.map v (polynomial P p q w y))
  rw [← FourEdgeTree.realized_comp, hv]
  exact attachment_parameter P p q w β hd y

/-- Source projection sends the one original sheet tip to the one original ordinary tip. -/
theorem erase_square :
    SSet.toTop.map (erase F) ≫ 𝟙 _ = vertex P p q w v ≫
      SSet.toTop.map (SSet.stdSimplex.isTerminalObj₀.from (FourEdgeTree.simplicial E Jd)) := by
  ext y
  exact Subsingleton.elim _ _

/-- This is the existing map of displayed double cylinders; its height coordinate is unchanged. -/
def map : C(CoefficientBassRaw1PolynomialPostcomp.carrier P p q w β,
    FourEdge.scalarCone P d E) :=
  (DoubleCylinder.map (first_isPushout F J G (Iso.refl _))
    (DoubleCylinder.realized_isPushout βd (SSet.stdSimplex.isTerminalObj₀.from _))
    (vertex P p q w v) (TopCat.ofHom (laurent P p q w β hd)) (𝟙 _)
    (attachment_square P p q w β hd v hv) (erase_square P p q w v)).hom

/-- The full Laurent baseline is transported with its proved original anchor. -/
theorem map_laurent (y : |parameterSSet G|) :
    map P p q w β hd v hv (SSet.toTop.map (left₀ F J G (Iso.refl _)) y) =
      FourEdgeTree.laurentInclusion E Jd H βd (laurent P p q w β hd y) := by
  have h₀ := congrArg (map P p q w β hd v hv)
    (FourEdgeTree.SetDescent.eval_realized_left
      (attaching F J G (Iso.refl _)) (erase F) y)
  have h₁ := DoubleCylinder.map_left (first_isPushout F J G (Iso.refl _))
    (DoubleCylinder.realized_isPushout βd (SSet.stdSimplex.isTerminalObj₀.from _))
    (vertex P p q w v) (TopCat.ofHom (laurent P p q w β hd)) (𝟙 _)
    (attachment_square P p q w β hd v hv) (erase_square P p q w v) y
  exact h₀.trans (h₁.trans (FourEdgeTree.SetDescent.eval_realized_left
    βd (SSet.stdSimplex.isTerminalObj₀.from _) (laurent P p q w β hd y)).symm)

/-- The original terminal point maps to the same ordinary cone tip. -/
theorem map_tip :
    map P p q w β hd v hv
      (SSet.toTop.map (right₀ F J G (Iso.refl _)) (default : |tipSSet.{u+1}|)) =
      FourEdgeTree.tip E Jd H βd := by
  have h₀ := congrArg (map P p q w β hd v hv)
    (FourEdgeTree.SetDescent.eval_realized_right
      (attaching F J G (Iso.refl _)) (erase F) (default : |tipSSet.{u+1}|))
  have h₁ := DoubleCylinder.map_right (first_isPushout F J G (Iso.refl _))
    (DoubleCylinder.realized_isPushout βd (SSet.stdSimplex.isTerminalObj₀.from _))
    (vertex P p q w v) (TopCat.ofHom (laurent P p q w β hd)) (𝟙 _)
    (attachment_square P p q w β hd v hv) (erase_square P p q w v) default
  exact h₀.trans (h₁.trans (FourEdgeTree.SetDescent.eval_realized_right
    βd (SSet.stdSimplex.isTerminalObj₀.from _) default).symm)

/-- Every source cylinder keeps its independent literal original height. -/
theorem map_cylinder (y : |parameterSSet F|) (t : I) :
    map P p q w β hd v hv
      (DoubleCylinder.realizedCylinder (attaching F J G (Iso.refl _)) (erase F)
        (y, ULift.up t)) =
      FourEdgeTree.cylinder E Jd H βd (vertex P p q w v y, t) :=
  DoubleCylinder.map_cylinder_apply _ _ _ _ _ _ _ _ _

/-- The positive chart uses its entire original polynomial vertex. -/
def plus : C(CoefficientBassRaw1PolynomialPostcomp.carrier P p q w (underToLaurent R),
    FourEdge.scalarCone P d E) :=
  map P p q w (underToLaurent R) (laurentPlus_projection P d)
    (FourEdgeTree.plusVertex E Jd) (FourEdge.beta_plus P d E)

/-- The inverse chart uses its own polynomial vertex and the same ordinary tip. -/
def minus : C(CoefficientBassRaw1PolynomialPostcomp.carrier P p q w (underToLaurentInvert R),
    FourEdge.scalarCone P d E) :=
  map P p q w (underToLaurentInvert R) (laurentMinus_projection P d)
    (FourEdgeTree.minusVertex E Jd) (FourEdge.beta_minus P d E)

end Quillen.PerfectComplexes.CoefficientBassRaw1PolynomialOrdinaryMap
