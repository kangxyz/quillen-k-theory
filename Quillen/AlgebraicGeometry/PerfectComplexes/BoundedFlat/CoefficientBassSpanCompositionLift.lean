/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassSpanCompositionTerminal
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeSpanComposition

/-! The complete scalar cylinder of the chosen coefficient span composition homotopy. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSpanCompositionReference
open CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (p : a ⟶ b) (q : b ⟶ c)
local notation "E" => coefficientReference P p q
local notation "J" => polynomialMap P (c := c)

/-- Only the endpoint proof changes; the entire second original polynomial path is retained. -/
def terminalSecondAttached : Path (polynomialVertex P p q 13)
    (SSet.toTop.map (FourEdgeTree.attachment E J) (coefficientPath P p q 1)) :=
  (terminalSecondPath P p q).cast rfl
    ((terminalSecondPath_attachment P p q).symm.trans (terminalSecondPath P p q).target)

/-- The original three-stage reassociation on all five full-reference leaves. -/
def treeReassociation := FourEdgeTree.spanReassociation E J (coefficientPath P p q 1)
  (terminalFirstPath P p q) (terminalSecondAttached P p q)

/-- The exact whole span-valued A cylinder, retaining its final reversed reassociation. -/
def treeComposition : C(I × I, FourEdgeTree.space E J) :=
  FourEdgeTree.spanComposition E J (coefficientPath P p q 1)
    (terminalFirstPath P p q) (terminalSecondAttached P p q)
    (polynomialSquare P p q) (coefficientPath P p q) (polynomialSquare_attachment P p q)
    rfl (polynomialSquare_terminal P p q)

theorem treeComposition_lower (r s : I) :
    treeComposition P p q (lower r, s) = treeSquare P p q (r, s) :=
  FourEdgeTree.spanComposition_lower E J _ _ _ _ _ _ _ _ r s

theorem treeComposition_upper (r s : I) :
    treeComposition P p q (upper r, s) = treeReassociation P p q (unitInterval.symm r, s) :=
  FourEdgeTree.spanComposition_upper E J _ _ _ _ _ _ _ _ r s

/-- The full positive chart edge keeps the original terminal half pause. -/
theorem treeComposition_left (r : I) :
    treeComposition P p q (r, 0) =
      ((FourEdgeTree.positiveChartPath E J (polynomialSquare P p q)).trans
        (Path.refl _)) r :=
  FourEdgeTree.spanComposition_left E J _ _ _ _ _ _ _ _ r

/-- The separate inverse chart has exactly the same original final pause. -/
theorem treeComposition_right (r : I) :
    treeComposition P p q (r, 1) =
      ((FourEdgeTree.negativeChartPath E J (polynomialSquare P p q)).trans
        (Path.refl _)) r :=
  FourEdgeTree.spanComposition_right E J _ _ _ _ _ _ _ _ r

/-- All five original native leaves, and all three original reassociation stages, are unchanged. -/
theorem treeReassociation_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdgeTree.nativeEval E J n (treeReassociation P p q (r, s)) x =
      (boundedFlatCoefficientPolynomialSpanReparameterization P p q).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (s, x)) := by
  let iL := HomotopyPushout.inl
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
  let iR := HomotopyPushout.inr
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
    (boundedFlatPerfectPrespectrumMap (polynomialProjection P c))
  let A := boundedFlatPerfectPrespectrumMap (coefficientMap P p)
  let C := boundedFlatPerfectPrespectrumMap (coefficientMap P q)
  let D := boundedFlatPerfectPrespectrumMap
    (coefficientMap P ((polynomialUnderFunctor R).map q))
  let H := boundedFlatCoefficientPolynomialSquareHomotopy P p
  let K := boundedFlatCoefficientPolynomialSquareHomotopy P q
  let pL := (terminalFirstPath P p q).map
    (SSet.toTop.map (FourEdgeTree.plusVertex E J)).hom.continuous
  let qL := (terminalSecondAttached P p q).map
    (SSet.toTop.map (FourEdgeTree.plusVertex E J)).hom.continuous
  let tL := FourEdgeTree.overlapPath E J (coefficientPath P p q 1)
  let qR := (terminalSecondAttached P p q).symm.map
    (SSet.toTop.map (FourEdgeTree.minusVertex E J)).hom.continuous
  let pR := (terminalFirstPath P p q).symm.map
    (SSet.toTop.map (FourEdgeTree.minusVertex E J)).hom.continuous
  let G := boundedFlatPerfectPrespectrumMap (polynomialProjection P b)
  let F := boundedFlatPerfectPrespectrumMap (polynomialProjection P c)
  let Q : Homotopy ((A ≫ G) ≫ (D ≫ iL)) ((A ≫ C) ≫ (F ≫ iL)) :=
    (Homotopy.precomp A (K.postcomp iL)).cast
    (by simp only [G, D, Category.assoc])
      (by simp only [C, F, Category.assoc])
  let U : Homotopy ((A ≫ C) ≫ (F ≫ iR)) ((A ≫ G) ≫ (D ≫ iR)) :=
    (Homotopy.precomp A (K.symm.postcomp iR)).cast
    (by simp only [C, F, Category.assoc])
      (by simp only [G, D, Category.assoc])
  refine Quillen.NativeSpanReassociation.word n x
    (fun z ↦ FourEdgeTree.nativeEval E J n z x)
    pL qL tL qR pR (H.postcomp (D ≫ iL)) Q
    (Homotopy.precomp (A ≫ C) (HomotopyPushout.glue _ _)) U (H.symm.postcomp (D ≫ iR))
    ?_ ?_ ?_ ?_ ?_ r s
  · intro t
    change FourEdgeTree.nativeEval E J n
      (SSet.toTop.map (FourEdgeTree.plusVertex E J) (terminalFirstPath P p q t)) x = _
    rw [FourEdgeTree.nativeEval_plus]
    exact congrArg (iL.map n) (terminalFirstPath_native P p q n t x)
  · intro t
    change FourEdgeTree.nativeEval E J n
      (SSet.toTop.map (FourEdgeTree.plusVertex E J) (terminalSecondPath P p q t)) x = _
    rw [FourEdgeTree.nativeEval_plus]
    exact congrArg (iL.map n) (terminalSecondPath_native P p q n t x)
  · intro t
    change FourEdgeTree.nativeEval E J n
      (FourEdgeTree.overlap E J (coefficientPath P p q 1, t)) x = _
    rw [FourEdgeTree.nativeEval_overlap]
    change HomotopyPushout.cylinder _ _ n
      (t, pointwisePrespectrumFamily E n (coefficientPath P p q 1) x) = _
    rw [coefficientPath_native, (boundedFlatCoefficientCompositionHomotopy P p q).at_one]; rfl
  · intro t
    change FourEdgeTree.nativeEval E J n
      (SSet.toTop.map (FourEdgeTree.minusVertex E J)
        (terminalSecondPath P p q (unitInterval.symm t))) x = _
    rw [FourEdgeTree.nativeEval_minus]
    exact congrArg (iR.map n) (terminalSecondPath_native P p q n (unitInterval.symm t) x)
  · intro t
    change FourEdgeTree.nativeEval E J n
      (SSet.toTop.map (FourEdgeTree.minusVertex E J)
        (terminalFirstPath P p q (unitInterval.symm t))) x = _
    rw [FourEdgeTree.nativeEval_minus]
    exact congrArg (iR.map n) (terminalFirstPath_native P p q n (unitInterval.symm t) x)

/-- The complete scalar cylinder evaluates to the literal original A, at every original input. -/
theorem treeComposition_native (n : ℕ) (r s : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    FourEdgeTree.nativeEval E J n (treeComposition P p q (r, s)) x =
      (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P p q).level n
        (r, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (s, x)) := by
  rcases cover r with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · rw [treeComposition_lower]
    exact (treeSquare_vertex_native P p q n t s x).trans
      (Homotopy.trans_lower_cell
        (boundedFlatCoefficientPolynomialSpanVertexCompositionHomotopy P p q)
        (boundedFlatCoefficientPolynomialSpanReparameterization P p q).symm n t _).symm
  · rw [treeComposition_upper]
    have ht := Homotopy.trans_upper_cell
      (boundedFlatCoefficientPolynomialSpanVertexCompositionHomotopy P p q)
      (boundedFlatCoefficientPolynomialSpanReparameterization P p q).symm n t
      (HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (s, x))
    change (boundedFlatCoefficientPolynomialSpanCompositionHomotopy P p q).level n
      (upper t, HomotopyPushout.cylinder
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
        (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (s, x)) =
      (boundedFlatCoefficientPolynomialSpanReparameterization P p q).level n
        (unitInterval.symm t, HomotopyPushout.cylinder
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a))
          (boundedFlatPerfectPrespectrumMap (polynomialProjection P a)) n (s, x)) at ht
    exact (treeReassociation_native P p q n (unitInterval.symm t) s x).trans ht.symm

end Quillen.PerfectComplexes.CoefficientBassSpanCompositionReference
