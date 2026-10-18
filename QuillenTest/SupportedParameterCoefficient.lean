/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedParameterCoefficientModels

/-!
# The actual supported Spec-row component

The row isomorphism retains the original support property, its selected zero, and
the complete coefficient naturality square on genuine supported sections.
-/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.BaseChange.Coefficients
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

example (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (S : (specUnder ⋙ ParameterModels.supported f.left).obj a) :
    rowSupported f a (((parameterSupportedRowIso f).hom.app a).functor.obj S).obj :=
  (((parameterSupportedRowIso f).hom.app a).functor.obj S).property

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    ((parameterSupportedRowIso f).hom.app a).functor.obj
        ((specUnder ⋙ ParameterModels.supported f.left).obj a).waldhausen.zero =
      ((supportedRow f).obj a).waldhausen.zero :=
  ((parameterSupportedRowIso f).hom.app a).zero

example {a b : Under (CommRingCat.of (ULift.{u} ℤ))} (g : a ⟶ b) :
    (ParameterModels.supported f.left).map (specUnder.map g) ≫
        (parameterSupportedRowIso f).hom.app b =
      (parameterSupportedRowIso f).hom.app a ≫ (supportedRow f).map g :=
  (parameterSupportedRowIso f).hom.naturality g

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) :
    (parameterSupportedRowIso f).hom.app a ≫ (parameterSupportedRowIso f).inv.app a =
      𝟙 ((specUnder ⋙ ParameterModels.supported f.left).obj a) :=
  (parameterSupportedRowIso f).hom_inv_id_app a
