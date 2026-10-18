/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedParameterTelescopeForget
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSupportedParameterTelescopeCells

/-!
# Actual supported Spec telescopes and their original fine forgetful map

The tests use arbitrary supported telescope points, rather than only stage inclusions.
They retain the specified inverse, actual coefficient naturality, and the original fine
supported-to-ambient quotient map.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.LoopPrespectrum
open Quillen.PerfectComplexes Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.GlobalSupportedParameterCoefficient
universe u
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))} (f : P ⟶ Q)
    [IsOpenImmersion f.left]

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : (parameterTelescope f.left).obj (specUnder.obj a) |>.space n) :
    ((telescopeIso f).inv.app a).map n (((telescopeIso f).hom.app a).map n x) = x :=
  congrArg (fun k => k.map n x) ((telescopeIso f).hom_inv_id_app a)

example {a b : Under (CommRingCat.of (ULift.{u} ℤ))} (g : a ⟶ b) :
    (parameterTelescope f.left).map (specUnder.map g) ≫ (telescopeIso f).hom.app b =
      (telescopeIso f).hom.app a ≫ (SupportedTelescope.globalTelescope f).map g :=
  (telescopeIso f).hom.naturality g

example (a : Under (CommRingCat.of (ULift.{u} ℤ))) (n : ℕ)
    (x : (parameterTelescope f.left).obj (specUnder.obj a) |>.space n) :
    ((GlobalParameterCoefficient.fineTelescopeComparison Q).app a).map n
        (((ParameterFullCurrentNull.iteratedForget f.left).app (specUnder.obj a)).map n x) =
      ((boundedFlatCoefficientSupportedBassTelescopeForget f).app a).map n
        (((fineTelescopeComparison f).app a).map n x) :=
  congrArg (fun k => k.map n x) (NatTrans.congr_app (fineTelescope_forget_square f) a)
