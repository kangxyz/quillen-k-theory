/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterDoubleCorrection

/-! The actual supported quotient criterion preserves arbitrary incoming original classes. -/
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.PerfectComplexes Quillen.KTheory.Bass.GeometricConeInterchange
universe u

example {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left] [CompactSpace Q.left]
    (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (h : AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.doubleContractionSwap
      (quasiCompactStableZero (GlobalSupportedParameterCoefficient.parameterDiagram f))
        (coefficientParameterScheme a) = -𝟙 _)
    {A : AddCommGrpCat.{u + 1}}
    (g : A ⟶ (Quillen.PerfectComplexes.Bass.supportedNegativeKFunctor 2).obj
      ((boundedFlatCoefficientQuasiCompactOpenPairRow f).obj a)) :
    g ≫ (GlobalSupportedParameterCoefficient.negativeClassCorrection f 2 a).hom = g := by
  rw [GlobalSupportedParameterCoefficient.negativeClassCorrection_two_hom_of_quotient_swap
    f a h, Category.comp_id]
