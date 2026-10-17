/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetSpanPolynomialNative
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.BassProjectionFourEdgeTargetSpanCells
public import Quillen.Waldhausen.SConstruction.Iterated.CommonReferenceNerveFourEdgeExt

/-! The complete target tree map retains the original half-quarter-quarter span clock. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.NativePathCells
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.TargetSpan
open BassH0Merge CommonReferenceNerve CommonReferenceNerve.CutOpenCarrier FourEdgeTree
open LoopPrespectrum LoopPrespectrum.HomotopyPushout
variable {R : CommRingCat.{u}} (P : Over (Spec R)) {a b : Under R} (f : a ⟶ b)
variable {V : Model.{u + 1}}
  (E : V ⟶ modelOf (boundedFlatPerfectWaldhausen (space (op P, a))))
local notation "Ja" => normalizedMap (polynomialProjection P a)
local notation "Jb" => normalizedMap (polynomialProjection P b)
local notation "Eb" => input P f E
local notation "H" => boundedFlatCoefficientPolynomialSquareHomotopy P f
local notation "M" => boundedFlatCoefficientPolynomialSpanMap P f

private theorem map_first (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (M).map n (cylinder (prespectrumMap Ja) (prespectrumMap Ja) n (lower t, x)) =
      (inl (prespectrumMap Jb) (prespectrumMap Jb)).map n ((H).level n (t, x)) :=
  mapOfHomotopies_first_half _ _ _ _ _ _ _ _ _ n t x

private theorem map_middle (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (M).map n (cylinder (prespectrumMap Ja) (prespectrumMap Ja) n (upper (lower t), x)) =
      cylinder (prespectrumMap Jb) (prespectrumMap Jb) n
        (t, (boundedFlatPerfectPrespectrumMap (coefficientMap P f)).map n x) := by
  let A := (H).postcomp (inl (prespectrumMap Jb) (prespectrumMap Jb))
  let K := Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P f))
    (glue (prespectrumMap Jb) (prespectrumMap Jb))
  let L := (H).symm.postcomp (inr (prespectrumMap Jb) (prespectrumMap Jb))
  exact (Homotopy.trans_upper_cell A (K.trans L) n (lower t) x).trans
    (Homotopy.trans_lower_cell K L n t x)

private theorem map_last (n : ℕ) (t : I)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (M).map n (cylinder (prespectrumMap Ja) (prespectrumMap Ja) n (upper (upper t), x)) =
      (inr (prespectrumMap Jb) (prespectrumMap Jb)).map n
        ((H).level n (unitInterval.symm t, x)) := by
  let A := (H).postcomp (inl (prespectrumMap Jb) (prespectrumMap Jb))
  let K := Homotopy.precomp (boundedFlatPerfectPrespectrumMap (coefficientMap P f))
    (glue (prespectrumMap Jb) (prespectrumMap Jb))
  let L := (H).symm.postcomp (inr (prespectrumMap Jb) (prespectrumMap Jb))
  exact (Homotopy.trans_upper_cell A (K.trans L) n (upper t) x).trans
    (Homotopy.trans_upper_cell K L n t x)

/-- The whole positive polynomial summand has its actual native coefficient image. -/
theorem treeMap_native_plus (n : ℕ) (y : |parameterSSet (E ≫ Ja)|)
    (x : (prespectrum V).space n) :
    nativeEval Eb Jb n (treeMap P f E (SSet.toTop.map (plusVertex E Ja) y)) x =
      (M).map n (nativeEval E Ja n (SSet.toTop.map (plusVertex E Ja) y) x) := by
  rw [treeMap_plus, nativeEval_plus]
  change nativeEval Eb Jb n (SSet.toTop.map (plusVertex Eb Jb)
    (polynomialMap P f E y)) x = _
  rw [nativeEval_plus]
  change (inl (prespectrumMap Jb) (prespectrumMap Jb)).map n
    (pointwisePrespectrumFamily (polynomialReference P f E) n (polynomialMap P f E y) x) = _
  rw [polynomialMap_native]
  exact (congrArg (fun k ↦ k.map n
    (pointwisePrespectrumFamily (E ≫ Ja) n y x))
      (inl_boundedFlatCoefficientPolynomialSpanMap P f)).symm

/-- The whole negative polynomial summand remains separate and has its actual coefficient image. -/
theorem treeMap_native_minus (n : ℕ) (y : |parameterSSet (E ≫ Ja)|)
    (x : (prespectrum V).space n) :
    nativeEval Eb Jb n (treeMap P f E (SSet.toTop.map (minusVertex E Ja) y)) x =
      (M).map n (nativeEval E Ja n (SSet.toTop.map (minusVertex E Ja) y) x) := by
  rw [treeMap_minus, nativeEval_minus]
  change nativeEval Eb Jb n (SSet.toTop.map (minusVertex Eb Jb)
    (polynomialMap P f E y)) x = _
  rw [nativeEval_minus]
  change (inr (prespectrumMap Jb) (prespectrumMap Jb)).map n
    (pointwisePrespectrumFamily (polynomialReference P f E) n (polynomialMap P f E y) x) = _
  rw [polynomialMap_native]
  exact (congrArg (fun k ↦ k.map n
    (pointwisePrespectrumFamily (E ≫ Ja) n y x))
      (inr_boundedFlatCoefficientPolynomialSpanMap P f)).symm

/-- Every original first-quarter input retains its unchanged polynomial square time. -/
theorem treeMap_native_edge12 (n : ℕ) (y : |parameterSSet E|) (t : I)
    (x : (prespectrum V).space n) :
    nativeEval Eb Jb n (treeMap P f E (realizedEdge (edge12 E Ja) (y, t))) x =
      (M).map n (nativeEval E Ja n (realizedEdge (edge12 E Ja) (y, t)) x) := by
  rw [treeMap_edge12, nativeEval_edge12]
  change nativeEval Eb Jb n (SSet.toTop.map (plusVertex Eb Jb)
    (polynomialSquare P f E (y, lower (unitInterval.symm t)))) x = _
  rw [nativeEval_plus]
  change (inl (prespectrumMap Jb) (prespectrumMap Jb)).map n
    (pointwisePrespectrumFamily (polynomialReference P f E) n
      (polynomialSquare P f E (y, lower (unitInterval.symm t))) x) = _
  rw [polynomialSquare_native]
  have ht : time12 t = lower (lower (unitInterval.symm t)) := by
    apply Subtype.ext
    change (1 - ((t : ℝ) + 1) / 2) / 2 = ((1 - (t : ℝ)) / 2) / 2
    ring
  change _ = (M).map n (cylinder _ _ n (time12 t, _))
  rw [ht]
  exact (map_first P f n (lower (unitInterval.symm t)) _).symm

/-- Every original second-quarter input retains the remaining positive square time. -/
theorem treeMap_native_edge01 (n : ℕ) (y : |parameterSSet E|) (t : I)
    (x : (prespectrum V).space n) :
    nativeEval Eb Jb n (treeMap P f E (realizedEdge (edge01 E Ja) (y, t))) x =
      (M).map n (nativeEval E Ja n (realizedEdge (edge01 E Ja) (y, t)) x) := by
  rw [treeMap_edge01, nativeEval_edge01]
  change nativeEval Eb Jb n (SSet.toTop.map (plusVertex Eb Jb)
    (polynomialSquare P f E (y, unitInterval.symm (lower t)))) x = _
  rw [nativeEval_plus]
  change (inl (prespectrumMap Jb) (prespectrumMap Jb)).map n
    (pointwisePrespectrumFamily (polynomialReference P f E) n
      (polynomialSquare P f E (y, unitInterval.symm (lower t))) x) = _
  rw [polynomialSquare_native]
  exact (map_first P f n (unitInterval.symm (lower t)) _).symm

/-- The original third quarter traverses the whole target overlap. -/
theorem treeMap_native_edge03 (n : ℕ) (y : |parameterSSet E|) (t : I)
    (x : (prespectrum V).space n) :
    nativeEval Eb Jb n (treeMap P f E (realizedEdge (edge03 E Ja) (y, t))) x =
      (M).map n (nativeEval E Ja n (realizedEdge (edge03 E Ja) (y, t)) x) := by
  rw [treeMap_edge03, nativeEval_edge03]
  change nativeEval Eb Jb n (overlap Eb Jb
    (mapParameter (postcompNode (coefficientPost P f)) y, t)) x = _
  rw [nativeEval_overlap]
  change cylinder (prespectrumMap Jb) (prespectrumMap Jb) n
    (t, pointwisePrespectrumFamily Eb n
      (SSet.toTop.map (attachment E (coefficientPost P f)) y) x) = _
  rw [attachment_native]
  exact (map_middle P f n t _).symm

/-- The last quarter retains the whole reversed negative square. -/
theorem treeMap_native_edge34 (n : ℕ) (y : |parameterSSet E|) (t : I)
    (x : (prespectrum V).space n) :
    nativeEval Eb Jb n (treeMap P f E (realizedEdge (edge34 E Ja) (y, t))) x =
      (M).map n (nativeEval E Ja n (realizedEdge (edge34 E Ja) (y, t)) x) := by
  rw [treeMap_edge34, nativeEval_edge34]
  change nativeEval Eb Jb n (SSet.toTop.map (minusVertex Eb Jb)
    (polynomialSquare P f E (y, unitInterval.symm t))) x = _
  rw [nativeEval_minus]
  change (inr (prespectrumMap Jb) (prespectrumMap Jb)).map n
    (pointwisePrespectrumFamily (polynomialReference P f E) n
      (polynomialSquare P f E (y, unitInterval.symm t)) x) = _
  rw [polynomialSquare_native]
  exact (map_last P f n t _).symm

/-- The actual whole tree map recovers the fixed original span map in every native degree. -/
theorem treeMap_native (n : ℕ) (z : FourEdgeTree.space E Ja) (x : (prespectrum V).space n) :
    nativeEval Eb Jb n (treeMap P f E z) x = (M).map n (nativeEval E Ja n z x) :=
  congrFun (funext_cells E Ja
    (fun z ↦ nativeEval Eb Jb n (treeMap P f E z) x)
    (fun z ↦ (M).map n (nativeEval E Ja n z x))
    (fun y ↦ treeMap_native_plus P f E n y x)
    (fun y ↦ treeMap_native_minus P f E n y x)
    (fun y t ↦ treeMap_native_edge12 P f E n y t x)
    (fun y t ↦ treeMap_native_edge01 P f E n y t x)
    (fun y t ↦ treeMap_native_edge03 P f E n y t x)
    (fun y t ↦ treeMap_native_edge34 P f E n y t x)) z

end Quillen.PerfectComplexes.BassProjectionPath.WholeReference.FourEdge.TargetSpan
