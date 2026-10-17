/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientBassPositiveJ0ConeBoundaries
public import Quillen.Topology.Prespectrum.RelativeHomotopyTerminalEvaluation

/-!
# Literal native identification of the two actual cone-boundary comparisons

The original conePasting is used unchanged, including its whole-level casts and the two-half
collapse followed by terminal-pause cancellation. The two carrier tips remain distinct.
This identifies one constituent of the original null recipe, not the assembled J0 comparison.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open CommRingCat.PolynomialLaurent AlgebraicGeometry.Scheme.BaseChange.Coefficients
open Quillen.Waldhausen.IteratedS
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.CoefficientBassPositiveJ0ConePasting
open CommonReferenceNerve CoefficientBassPositiveJ0ConeBoundaries
variable {R : CommRingCat.{u}} (P : Over (Spec R)) (d : Under R)

private theorem relativeTrans_level_apply {E F : Quillen.LoopPrespectrum.{u}}
    {f g : E ⟶ F} {H K L : Quillen.LoopPrespectrum.Homotopy f g}
    (J : H.RelHomotopy K) (J' : K.RelHomotopy L)
    (n : ℕ) (r s : I) (x : E.space n) :
    (J.trans J').level n (r, (s, x)) =
      ((J.level n).trans (J'.level n)) (r, (s, x)) := rfl

/-- Both halves agree with the original native conePasting at every original coordinate. -/
theorem nativeSquare_conePasting (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    (nativeSquare P d n x).coneBoundary (r, s) =
      (CoefficientBassPositiveNullTrack.conePasting P (arrow d)).level n (r, (s, x)) := by
  rw [CarrierPathSquare.Square.coneBoundary_apply]
  unfold CoefficientBassPositiveNullTrack.conePasting
  rw [relativeTrans_level_apply, ContinuousMap.HomotopyRel.trans_apply]
  split_ifs with h
  · rw [LoopPrespectrum.Homotopy.RelHomotopy.ofLevels_apply,
      LoopPrespectrum.Homotopy.Square.toBoundary_apply]
    rfl
  · rw [LoopPrespectrum.Homotopy.RelHomotopy.transRefl_apply_path,
      LoopPrespectrum.Homotopy.path_trans]

/-- The entire actual minus cone boundary evaluates to the unchanged original conePasting. -/
theorem coneBoundaryMinus_conePasting (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (coneBoundaryMinus P d (r, s)) x =
      (CoefficientBassPositiveNullTrack.conePasting P (arrow d)).level n (r, (s, x)) :=
  (coneBoundaryMinus_native P d n r s x).trans (nativeSquare_conePasting P d n r s x)

/-- The entire actual plus cone boundary evaluates to the unchanged original conePasting. -/
theorem coneBoundaryPlus_conePasting (n : ℕ) (r s : I)
    (x : (prespectrum (modelOf (boundedFlatPerfectWaldhausen (space (op P, d))))).space n) :
    CutOpenCarrier.nativeEval (polyRef P d) (chart P d) (laurentRef P d)
      (ordinary P d) (shifted P d) n (coneBoundaryPlus P d (r, s)) x =
      (CoefficientBassPositiveNullTrack.conePasting P (arrow d)).level n (r, (s, x)) :=
  (coneBoundaryPlus_native P d n r s x).trans (nativeSquare_conePasting P d n r s x)

end Quillen.PerfectComplexes.CoefficientBassPositiveJ0ConePasting
