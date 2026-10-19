/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterFiniteNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalAuxiliaryParameterTelescopeComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterAuxiliaryTelescopeNull
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.CoefficientSupportedFullOpenBassLocalization

/-! # The same original auxiliary G7 null on the complete integral Spec-row telescope -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent.IntegerSpec
open Quillen.LoopPrespectrum Quillen.KTheory.Bass
universe u
namespace Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
open GlobalSectionChangeIndex
variable {P Q : Over (Spec (CommRingCat.of (ULift.{u} ℤ)))}
    (f : P ⟶ Q) [IsOpenImmersion f.left] (T : Q.left.Opens)

/-- The actual three supported Spec-row comparisons retain every original G7 full-null value. -/
theorem telescope_fullNull_square (a : Under (CommRingCat.of (ULift.{u} ℤ)))
    (n : ℕ) (s : unitInterval)
    (x : ((SchemeNaturalSeed.iteratedTelescope
      (ParameterAuxiliarySupport.fiberAction f.left T)).obj (specUnder.obj a)).space n) :
    ((openTelescopeComparison f T).app a).map n
      (((ParameterAuxiliarySupport.iteratedNull f.left T).homotopy
        (specUnder.obj a)).level n (s, x)) =
      ((boundedFlatCoefficientSupportedFiberBassTelescopeFullOpenNull f T).homotopy a).level n
        (s, ((fiberTelescopeComparison f T).app a).map n x) := by
  induction x using Quot.inductionOn with
  | h z =>
    exact congrArg (fun y => Telescope.cylinder
      (fun i => (boundedFlatCoefficientSupportedFullOpenBassDiagram f T i).obj a)
      (fun i => (boundedFlatCoefficientSupportedFullOpenBassTransition f T i).app a)
      n z.1 (z.2.1, y)) (finite_fullNull_square f T z.1 a n s z.2.2)

end Quillen.PerfectComplexes.GlobalAuxiliaryParameterCoefficient
