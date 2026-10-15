/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassCoherence
/-!
# Coefficient Bass Span Composition

Composition of the actual original coefficient polynomial-span maps.
The geometric rectangle is imported from its maintained owner.
-/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Quillen.LoopPrespectrum
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
universe u
namespace Quillen.PerfectComplexes
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- Rotate the maintained rectangle to the literal moving coefficient-composition boundary. -/
def boundedFlatCoefficientPolynomialCompositionBoundary :
    (boundedFlatCoefficientPolynomialSquareHomotopy P (u ≫ v)).RelHomotopy
      (((boundedFlatCoefficientPolynomialTargetCompositionTrack P u v).trans
        (boundedFlatCoefficientPolynomialCompositeSquare P u v)).trans
        (boundedFlatCoefficientPolynomialSourceCompositionTrack P u v).symm) := by
  let B := boundedFlatCoefficientPolynomialTargetCompositionTrack P u v
  let A := boundedFlatCoefficientPolynomialSourceCompositionTrack P u v
  let H := boundedFlatCoefficientPolynomialSquareHomotopy P (u ≫ v)
  let K := boundedFlatCoefficientPolynomialCompositeSquare P u v
  have J := boundedFlatCoefficientPolynomialSquareCompositionComparison P u v
  have route : (B.trans K).RelHomotopy (H.trans A) :=
    ((Homotopy.RelHomotopy.refl B).hcomp J).trans
      (((Homotopy.RelHomotopy.transAssoc B (B.symm.trans H) A).symm).trans
        ((((Homotopy.RelHomotopy.transAssoc B B.symm H).symm).hcomp
          (Homotopy.RelHomotopy.refl A)).trans
          ((((Homotopy.RelHomotopy.reflTransSymm B).symm.hcomp
            (Homotopy.RelHomotopy.refl H)).hcomp (Homotopy.RelHomotopy.refl A)).trans
            ((Homotopy.RelHomotopy.reflTrans H).hcomp (Homotopy.RelHomotopy.refl A)))))
  exact (Homotopy.RelHomotopy.transRefl H).symm.trans
    (((Homotopy.RelHomotopy.refl H).hcomp (Homotopy.RelHomotopy.reflTransSymm A)).trans
      (((Homotopy.RelHomotopy.transAssoc H A A.symm).symm).trans
        (route.symm.hcomp (Homotopy.RelHomotopy.refl A.symm))))

/-- The whole square retains direct and composed geometric tracks and both actual side tracks. -/
def boundedFlatCoefficientPolynomialCompositionSquare :=
  (boundedFlatCoefficientPolynomialCompositionBoundary P u v).toSquare

/-- Association casts give the literal composite-vertex span-map interface. -/
def boundedFlatCoefficientPolynomialCompositeDescSquare :=
  (boundedFlatCoefficientPolynomialCompositeSquare P u v).cast (Category.assoc _ _ _) rfl

/-- The composed vertex maps with the original pasted two square tracks. -/
def boundedFlatCoefficientPolynomialCompositeSpanMap :=
  HomotopyPushout.mapOfHomotopies
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P u) ≫
      boundedFlatPerfectPrespectrumMap (coefficientMap P v))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
      boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
      boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (boundedFlatCoefficientPolynomialCompositeDescSquare P u v)
    (boundedFlatCoefficientPolynomialCompositeDescSquare P u v)

/-- The direct original full span cylinder, without changing its parameterization. -/
def boundedFlatCoefficientPolynomialDirectSpanTrack :=
  HomotopyPushout.mapSquareHomotopy
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P (u ≫ v)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v))))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map (u ≫ v))))
    (boundedFlatCoefficientPolynomialSquareHomotopy P (u ≫ v))
    (boundedFlatCoefficientPolynomialSquareHomotopy P (u ≫ v))

/-- The original composite-vertex span cylinder, retaining the two pasted square tracks. -/
def boundedFlatCoefficientPolynomialComposedSpanTrack :=
  HomotopyPushout.mapSquareHomotopy
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P u) ≫
      boundedFlatPerfectPrespectrumMap (coefficientMap P v))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
      boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
      boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (boundedFlatCoefficientPolynomialCompositeDescSquare P u v)
    (boundedFlatCoefficientPolynomialCompositeDescSquare P u v)

/-- The left native polynomial chart moves through the unchanged original composition track. -/
def boundedFlatCoefficientPolynomialSpanLeftCompositionTrack :=
  (boundedFlatCoefficientPolynomialCompositionHomotopy P u v).postcomp
    (HomotopyPushout.inl
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P c)))

/-- The right native polynomial chart moves through the same original composition track. -/
def boundedFlatCoefficientPolynomialSpanRightCompositionTrack :=
  (boundedFlatCoefficientPolynomialCompositionHomotopy P u v).postcomp
    (HomotopyPushout.inr
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
      (boundedFlatPerfectPrespectrumMap (polynomialProjection P c)))

/-- The actual two moving polynomial squares and original middle cylinder form a whole square. -/
def boundedFlatCoefficientPolynomialSpanCompositionSquare :
    (boundedFlatCoefficientPolynomialDirectSpanTrack P u v).Square
      (boundedFlatCoefficientPolynomialComposedSpanTrack P u v)
      (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatCoefficientPolynomialSpanLeftCompositionTrack P u v))
      (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatCoefficientPolynomialSpanRightCompositionTrack P u v)) := by
  let S := (boundedFlatCoefficientPolynomialCompositionSquare P u v).ofBoundaryLevels
    (boundedFlatCoefficientPolynomialSquareHomotopy P (u ≫ v))
    (boundedFlatCoefficientPolynomialCompositeDescSquare P u v)
    (Homotopy.precomp (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
      (boundedFlatCoefficientPolynomialCompositionHomotopy P u v))
    (boundedFlatCoefficientPolynomialSourceCompositionTrack P u v)
    (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
  exact HomotopyPushout.identicalLegMovingSquare
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
    (boundedFlatCoefficientPolynomialSquareHomotopy P (u ≫ v))
    (boundedFlatCoefficientPolynomialCompositeDescSquare P u v)
    (boundedFlatCoefficientCompositionHomotopy P u v)
    (boundedFlatCoefficientPolynomialCompositionHomotopy P u v) S

/-- Direct coefficient composition maps to the actual span with composed vertices and tracks. -/
def boundedFlatCoefficientPolynomialSpanVertexCompositionHomotopy :
    Homotopy (boundedFlatCoefficientPolynomialSpanMap P (u ≫ v))
      (boundedFlatCoefficientPolynomialCompositeSpanMap P u v) :=
  HomotopyPushout.descSquareHomotopy
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatCoefficientPolynomialSpanLeftCompositionTrack P u v)
    (boundedFlatCoefficientPolynomialSpanRightCompositionTrack P u v)
    (boundedFlatCoefficientPolynomialSpanCompositionSquare P u v)

/-- The exact original span-map composite differs only by the proved five-piece
    reparameterization. -/
def boundedFlatCoefficientPolynomialSpanReparameterization :
    Homotopy
      (boundedFlatCoefficientPolynomialSpanMap P u ≫ boundedFlatCoefficientPolynomialSpanMap P v)
      (boundedFlatCoefficientPolynomialCompositeSpanMap P u v) :=
  HomotopyPushout.identicalLegCompositionHomotopy
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P b))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P u))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map u)))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P v))
    (boundedFlatPerfectPrespectrumMap (coefficientMap P ((polynomialUnderFunctor R).map v)))
    (boundedFlatCoefficientPolynomialSquareHomotopy P u)
    (boundedFlatCoefficientPolynomialSquareHomotopy P v)

/-- Whole composition of the actual original native coefficient polynomial-span maps.
The first stage is the existing geometric rectangle; the second retains all five original
cylinder pieces and removes only their differing parenthesization in homotopy time. -/
def boundedFlatCoefficientPolynomialSpanCompositionHomotopy :
    Homotopy (boundedFlatCoefficientPolynomialSpanMap P (u ≫ v))
      (boundedFlatCoefficientPolynomialSpanMap P u ≫ boundedFlatCoefficientPolynomialSpanMap P v) :=
  (boundedFlatCoefficientPolynomialSpanVertexCompositionHomotopy P u v).trans
    (boundedFlatCoefficientPolynomialSpanReparameterization P u v).symm

/-- The original left chart follows its whole coefficient composition track, then the fixed face. -/
theorem boundedFlatCoefficientPolynomialSpanCompositionHomotopy_inl
    (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v).level n
      (r, (HomotopyPushout.inl
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x) =
      ((boundedFlatCoefficientPolynomialSpanLeftCompositionTrack P u v).trans
        (Quillen.LoopPrespectrum.Homotopy.refl
          ((boundedFlatPerfectPrespectrumMap
              (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
            boundedFlatPerfectPrespectrumMap
              (coefficientMap P ((polynomialUnderFunctor R).map v))) ≫
              HomotopyPushout.inl
                (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
                (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))))).level n (r,
                    x) := by
  change (((boundedFlatCoefficientPolynomialSpanVertexCompositionHomotopy P u v).levelHomotopy
      n).trans
    (((boundedFlatCoefficientPolynomialSpanReparameterization P u v).symm).levelHomotopy n)) _ =
      ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) _
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split <;> rfl

/-- The distinct original right chart retains the same composition time and its own inclusion. -/
theorem boundedFlatCoefficientPolynomialSpanCompositionHomotopy_inr
    (n : ℕ) (r : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (polynomialUnderFunctor R).obj a)))).space n) :
    (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P u v).level n
      (r, (HomotopyPushout.inr
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))).map n x) =
      ((boundedFlatCoefficientPolynomialSpanRightCompositionTrack P u v).trans
        (Quillen.LoopPrespectrum.Homotopy.refl
          ((boundedFlatPerfectPrespectrumMap
              (coefficientMap P ((polynomialUnderFunctor R).map u)) ≫
            boundedFlatPerfectPrespectrumMap
              (coefficientMap P ((polynomialUnderFunctor R).map v))) ≫
              HomotopyPushout.inr
                (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
                (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))))).level n (r,
                    x) := by
  change (((boundedFlatCoefficientPolynomialSpanVertexCompositionHomotopy P u v).levelHomotopy
      n).trans
    (((boundedFlatCoefficientPolynomialSpanReparameterization P u v).symm).levelHomotopy n)) _ =
      ((Homotopy.levelHomotopy _ n).trans (Homotopy.levelHomotopy _ n)) _
  rw [ContinuousMap.HomotopyRel.trans_apply, ContinuousMap.HomotopyRel.trans_apply]
  split <;> rfl

end Quillen.PerfectComplexes
