/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MFiveNativePaths

/-! Exact whole original second M stage in the unchanged H1 common family. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite Convexity
open Quillen.PolynomialBaseChange AlgebraicGeometry.Scheme.CoefficientBaseChange
open Quillen.Waldhausen.IteratedS Quillen.LoopPrespectrum Quillen.NativePathCells
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMReassociation
variable {R : CommRingCat.{u}} (P : Over (Spec R))
variable {a b c : Under R} (u : a ⟶ b) (v : b ⟶ c)

/-- The very three-associator word used in the original native span-map composition. -/
def nativeReassociation :
    ((nativeP P u v).trans (((nativeQ P u v).trans
      ((nativeT P u v).trans (nativeU P u v))).trans (nativeV P u v))).RelHomotopy
    (((nativeP P u v).trans (nativeQ P u v)).trans
      ((nativeT P u v).trans ((nativeU P u v).trans (nativeV P u v)))) :=
  ((Homotopy.RelHomotopy.refl (nativeP P u v)).hcomp
    (Homotopy.RelHomotopy.transAssoc (nativeQ P u v)
      ((nativeT P u v).trans (nativeU P u v)) (nativeV P u v))).trans
    (((Homotopy.RelHomotopy.refl (nativeP P u v)).hcomp
      ((Homotopy.RelHomotopy.refl (nativeQ P u v)).hcomp
        (Homotopy.RelHomotopy.transAssoc (nativeT P u v) (nativeU P u v) (nativeV P u v)))).trans
      (Homotopy.RelHomotopy.transAssoc (nativeP P u v) (nativeQ P u v)
        ((nativeT P u v).trans ((nativeU P u v).trans (nativeV P u v)))).symm)

/-- Whole scalar and original native reassociations agree for all parameters and all levels. -/
theorem reassociation_lift : PostmappedSimplexLift.HomotopyLift (BassH1Merged.simplex P u v)
    (boundedFlatCoefficientBassSquareComparison P c) reassociation (nativeReassociation P u v) := by
  let S := BassH1Merged.simplex P u v
  let B := boundedFlatCoefficientBassSquareComparison P c
  have lP := P_native P u v
  have lQ := Q_native P u v
  have lT := T_native P u v
  have lU := U_native P u v
  have lV := V_native P u v
  have step₁ := PostmappedSimplexLift.HomotopyLift.hcomp S B
    (PostmappedSimplexLift.PathLift.refl S B lP)
    (PostmappedSimplexLift.PathLift.transAssoc S B lQ
      (PostmappedSimplexLift.PathLift.trans S B lT lU) lV)
  have step₂ := PostmappedSimplexLift.HomotopyLift.hcomp S B
    (PostmappedSimplexLift.PathLift.refl S B lP)
    (PostmappedSimplexLift.HomotopyLift.hcomp S B
      (PostmappedSimplexLift.PathLift.refl S B lQ)
      (PostmappedSimplexLift.PathLift.transAssoc S B lT lU lV))
  have step₃ := PostmappedSimplexLift.HomotopyLift.symm S B
    (PostmappedSimplexLift.PathLift.transAssoc S B lP lQ
      (PostmappedSimplexLift.PathLift.trans S B lT
        (PostmappedSimplexLift.PathLift.trans S B lU lV)))
  exact PostmappedSimplexLift.HomotopyLift.trans S B step₁
    (PostmappedSimplexLift.HomotopyLift.trans S B step₂ step₃)

/-- Original quotient descent evaluates the literal reparameterization on every cylinder. -/
theorem reparameterization_cylinder (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (boundedFlatCoefficientPolynomialSpanReparameterization P u v).level n
      (r, HomotopyPushout.cylinder (projectionMap P a) (projectionMap P a) n (t, x)) =
    (nativeReassociation P u v).level n (r, (t, x)) := rfl

/-- The second original half is precisely the reversed original reassociation, at native speed. -/
theorem originalM_upper (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    (BassMComponents.originalM P u v).level n
      (upper r, HomotopyPushout.cylinder (projectionMap P a) (projectionMap P a) n (t, x)) =
    (boundedFlatCoefficientBassSquareComparison P c).map n
      ((nativeReassociation P u v).level n (unitInterval.symm r, (t, x))) := by
  change (boundedFlatCoefficientBassSquareComparison P c).map n
    (((boundedFlatCoefficientPolynomialSpanVertexCompositionHomotopy P u v).trans
      (boundedFlatCoefficientPolynomialSpanReparameterization P u v).symm).level n
        (upper r, _)) = _
  rw [Homotopy.trans_upper_cell]
  rfl

/-- Pure second-stage scalar parameters use the actual reversed original three-associator word. -/
def secondParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 131)) :=
  reassociation.symm.toContinuousMap

/-- Every parameter in the complete second half evaluates to the original M face. -/
theorem second_native (n : ℕ) (r t : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (BassH1Merged.simplex P u v) n (secondParameter (r, t), x) =
    (BassMComponents.originalM P u v).level n
      (upper r, HomotopyPushout.cylinder (projectionMap P a) (projectionMap P a) n (t, x)) :=
  (reassociation_lift P u v n (unitInterval.symm r) t x).trans
    (originalM_upper P u v n r t x).symm

/-- The whole final scalar edge is the unchanged fixed H1 target parameter. -/
theorem second_one (t : unitInterval) :
    secondParameter (1, t) = BassH1Order.h1Parameter.{u} (1, t) :=
  (reassociation.symm.apply_one t).trans (h1_target_word t).symm

/-- The entire second stage has its literal five-piece target as its initial path. -/
theorem second_zero (t : unitInterval) :
    secondParameter (0, t) = ((Ppath.trans Qpath).trans (Tpath.trans (Upath.trans Vpath))) t :=
  reassociation.symm.apply_zero t

/-- Every second-stage parameter retains the original based value. -/
theorem second_point (n : ℕ) (r t : unitInterval) :
    prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
      (secondParameter (r, t),
        (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).point n) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))).point n :=
  BassH1Merged.family_point P u v n _

/-- Structure time is independent of both original second-stage parameters, including level zero. -/
theorem second_structure (n : ℕ) (r t z : unitInterval)
    (x : (originalPrespectrum (boundedFlatPerfectWaldhausen (space (op P, a)))).space n) :
    prespectrumSimplexFamily (BassH1Merged.simplex P u v) (n + 1)
      (secondParameter (r, t),
        (originalPrespectrum (boundedFlatPerfectWaldhausen
          (space (op P, a)))).structureMap n x z) =
    (originalPrespectrum (boundedFlatPerfectWaldhausen
      (space (op P, (laurentUnderFunctor R).obj c)))).structureMap n
        (prespectrumSimplexFamily (BassH1Merged.simplex P u v) n
          (secondParameter (r, t), x)) z :=
  BassH1Merged.family_structure P u v n _ x z

end Quillen.PerfectComplexes.BassMReassociation
