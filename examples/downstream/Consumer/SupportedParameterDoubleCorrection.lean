/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedParameterDoubleCorrection

/-! External consumers keep the actual supported quotient and independently defined correction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.KTheory.Bass.GeometricConeInterchange
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
  [IsOpenImmersion f.left] [CompactSpace P.left] [CompactSpace Q.left]
  [QuasiSeparatedSpace Q.left]

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    Scheme.PolynomialLaurent.Relative.doubleContractionSwap
      (quasiCompactStableZero (GlobalSupportedParameterCoefficient.parameterDiagram f))
      (coefficientParameterScheme a) = -𝟙 _ :=
  SupportedParameterCoefficientUnitOperation.parameterDiagram_quotient_swap f a

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (GlobalSupportedParameterCoefficient.negativeClassCorrection f 2 a).inv = 𝟙 _ := by
  have h : GlobalSupportedParameterCoefficient.negativeClassCorrection f 2 a = Iso.refl _ := by
    apply Iso.ext
    exact GlobalSupportedParameterCoefficient.negativeClassCorrection_two_hom f a
  exact congrArg Iso.inv h
