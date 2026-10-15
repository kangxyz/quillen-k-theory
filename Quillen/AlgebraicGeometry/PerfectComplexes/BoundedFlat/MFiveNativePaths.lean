/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Aglib.Algebra.Polynomial.Laurent.UnderSquare
public import Quillen.Topology.Prespectrum.MPostmappedLift

/-! The actual five native paths in the original span-map reassociation. -/
@[expose] public section

open CommRingCat.PolynomialLaurent

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.NativePathCells
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMReassociation
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The map on bounded flat perfect prespectra induced by the polynomial projection at `d`. -/
abbrev projectionMap (d : Under R) := boundedFlatPerfectPrespectrumMap (polynomialProjection P d)
/-- The map on bounded flat perfect prespectra induced by the coefficient map along `u`. -/
abbrev overlapMap := boundedFlatPerfectPrespectrumMap (coefficientMap P u)
/--
The map on bounded flat perfect prespectra induced by the polynomial coefficient map along `u`.
-/
abbrev polynomialMap := boundedFlatPerfectPrespectrumMap
  (coefficientMap P ((polynomialUnderFunctor R).map u))
/--
The left inclusion into the homotopy pushout of the polynomial projection map at `d` with
itself.
-/
abbrev leftMap (d : Under R) := HomotopyPushout.inl (projectionMap P d) (projectionMap P d)
/--
The right inclusion into the homotopy pushout of the polynomial projection map at `d` with
itself.
-/
abbrev rightMap (d : Under R) := HomotopyPushout.inr (projectionMap P d) (projectionMap P d)

/-- The first literal square, followed by the original second chart map and left inclusion. -/
abbrev nativeP := (boundedFlatCoefficientPolynomialSquareHomotopy P u).postcomp
  (polynomialMap P v ≫ leftMap P c)

/-- The second literal square, with precisely the original endpoint transports. -/
def nativeQ :
    Homotopy ((overlapMap P u ≫ projectionMap P b) ≫ (polynomialMap P v ≫ leftMap P c))
      ((overlapMap P u ≫ overlapMap P v) ≫ (projectionMap P c ≫ leftMap P c)) :=
  (Homotopy.precomp (overlapMap P u)
    ((boundedFlatCoefficientPolynomialSquareHomotopy P v).postcomp (leftMap P c))).cast
      (by simp only [Category.assoc]) (by simp only [Category.assoc])

/-- The original central cylinder following both overlap maps. -/
abbrev nativeT := Homotopy.precomp (overlapMap P u ≫ overlapMap P v)
  (HomotopyPushout.glue (projectionMap P c) (projectionMap P c))

/-- The distinct inverse square with the original reversal and endpoint transports. -/
def nativeU :
    Homotopy ((overlapMap P u ≫ overlapMap P v) ≫ (projectionMap P c ≫ rightMap P c))
      ((overlapMap P u ≫ projectionMap P b) ≫ (polynomialMap P v ≫ rightMap P c)) :=
  (Homotopy.precomp (overlapMap P u)
    ((boundedFlatCoefficientPolynomialSquareHomotopy P v).symm.postcomp (rightMap P c))).cast
      (by simp only [Category.assoc]) (by simp only [Category.assoc])

/-- The original final reversed square followed by the second inverse chart map. -/
abbrev nativeV := (boundedFlatCoefficientPolynomialSquareHomotopy P u).symm.postcomp
  (polynomialMap P v ≫ rightMap P c)

/-- All first-path values are the original native positive composite piece. -/
theorem P_native : PostmappedSimplexLift.PathLift (BassH1Merged.simplex P u v)
    (boundedFlatCoefficientBassSquareComparison P c) Ppath (nativeP P u v) := by
  intro n t x
  rw [P_value, BassH1Merged.plus_product_family, BassH1Components.plus_native]
  rw [(boundedFlatCoefficientPlusSquareHomotopy P v).at_one]
  rfl

/-- All second-path values are the second native polynomial square on the original overlap input. -/
theorem Q_native : PostmappedSimplexLift.PathLift (BassH1Merged.simplex P u v)
    (boundedFlatCoefficientBassSquareComparison P c) Qpath (nativeQ P u v) := by
  intro n t x
  rw [Q_value, BassH1Merged.middle_family, BassH1Components.middle_native]
  rw [(boundedFlatCoefficientBassComparisonHomotopy P v).at_one]
  change (boundedFlatCoefficientBassSquareComparison P c).map n
    ((boundedFlatCoefficientPolynomialSpanMap P v).map n
      (HomotopyPushout.cylinder (projectionMap P b) (projectionMap P b) n
        (lower t, (overlapMap P u).map n x))) = _
  rw [BassH1NativeCells.span_lower]
  rfl

/-- The middle path is the literal target cylinder on the two original coefficient images. -/
theorem T_native : PostmappedSimplexLift.PathLift (BassH1Merged.simplex P u v)
    (boundedFlatCoefficientBassSquareComparison P c) Tpath (nativeT P u v) := by
  intro n t x
  rw [T_value, BassH1Merged.middle_family, BassH1Components.middle_native]
  rw [(boundedFlatCoefficientBassComparisonHomotopy P v).at_one]
  change (boundedFlatCoefficientBassSquareComparison P c).map n
    ((boundedFlatCoefficientPolynomialSpanMap P v).map n
      (HomotopyPushout.cylinder (projectionMap P b) (projectionMap P b) n
        (upper (lower t), (overlapMap P u).map n x))) = _
  rw [BassH1NativeCells.span_middle]
  rfl

/-- The full inverse middle path retains its actual reversed-square values. -/
theorem U_native : PostmappedSimplexLift.PathLift (BassH1Merged.simplex P u v)
    (boundedFlatCoefficientBassSquareComparison P c) Upath (nativeU P u v) := by
  intro n t x
  rw [U_value, BassH1Merged.middle_family, BassH1Components.middle_native]
  rw [(boundedFlatCoefficientBassComparisonHomotopy P v).at_one]
  change (boundedFlatCoefficientBassSquareComparison P c).map n
    ((boundedFlatCoefficientPolynomialSpanMap P v).map n
      (HomotopyPushout.cylinder (projectionMap P b) (projectionMap P b) n
        (upper (upper t), (overlapMap P u).map n x))) = _
  rw [BassH1NativeCells.span_upper]
  rfl

/-- All final-path values are the original distinct inverse composite piece. -/
theorem V_native : PostmappedSimplexLift.PathLift (BassH1Merged.simplex P u v)
    (boundedFlatCoefficientBassSquareComparison P c) Vpath (nativeV P u v) := by
  intro n t x
  rw [V_value, BassH1Merged.minus_product_family, BassH1Components.minus_native]
  rw [(boundedFlatCoefficientMinusSquareHomotopy P v).at_one]
  rfl

end Quillen.PerfectComplexes.BassMReassociation
