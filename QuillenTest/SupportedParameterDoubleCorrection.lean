/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedParameterDoubleCorrection

/-! Regression consumers of the actual supported Spec comparison and original class correction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Quillen.PerfectComplexes
open Quillen.PerfectComplexes.SupportedParameterCoefficientUnitOperation
open Quillen.PerfectComplexes.SupportedParameterSpecQuotientTransport
open Quillen.Bass.TwoChart
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Epi ((contractionMap (NatTrans.op Scheme.PolynomialLaurent.Relative.plus)
      (NatTrans.op Scheme.PolynomialLaurent.Relative.minus)
      (contractionMap (NatTrans.op Scheme.PolynomialLaurent.Relative.plus)
        (NatTrans.op Scheme.PolynomialLaurent.Relative.minus)
        (doubleForwardQuotient f.left))).app (specRow.obj a)) := by
  have := doubleForwardQuotient_doubleMap_spec_isIso f a
  infer_instance

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    GlobalSupportedParameterCoefficient.negativeClassCorrection f 2 a = Iso.refl _ := by
  apply Iso.ext
  exact GlobalSupportedParameterCoefficient.negativeClassCorrection_two_hom f a

example {X Y : Scheme.QuasiCompactSchemes.{u}ᵒᵖ} (g : X ⟶ Y) :
    (quasiCompactStableFunctor f.left 0).map g ≫ (doubleForwardQuotient f.left).app Y =
      (doubleForwardQuotient f.left).app X ≫
        (contraction (NatTrans.op Scheme.PolynomialLaurent.Relative.plus)
          (NatTrans.op Scheme.PolynomialLaurent.Relative.minus)
          (contraction (NatTrans.op Scheme.PolynomialLaurent.Relative.plus)
            (NatTrans.op Scheme.PolynomialLaurent.Relative.minus)
            (quasiCompactStableFunctor f.left 2))).map g :=
  (doubleForwardQuotient f.left).naturality g
