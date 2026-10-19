/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitRawInputSquare

/-! # The original tensor input square on the actual parameter products

The geometric square and its multiplication are specialized before introducing any evaluation
inverse. The projected Laurent coordinate is transported by its original pullback equation.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u
namespace Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open Quillen.KTheory.Bass.GeometricSeedCospan

/-- The original product map for a coefficient-index arrow. -/
def inputSchemeMap (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    scheme Q Y ⟶ scheme Q X :=
  ((baseProductFunctor (toIntegerBase Q)).op.map g).unop

/-- The original Laurent projection square on the actual parameter products. -/
theorem coefficientMap_input (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    inputSchemeMap Q (laurent.op.map g) ≫ coefficientMap Q X =
      coefficientMap Q Y ≫ inputSchemeMap Q g := by
  have h := congrArg
    (fun k : X ⟶ laurent.op.obj Y => ((baseProductFunctor (toIntegerBase Q)).op.map k).unop)
    (coefficient.naturality g)
  simpa only [inputSchemeMap, coefficientMap, Functor.map_comp, unop_comp, Functor.id_map,
    scheme] using h.symm

/-- The independently constructed genuine tensor square on those products. -/
def rawInputIso (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :=
  tensorUnitRawInputIso (coefficientMap Q X) (coefficientMap Q Y)
    (inputSchemeMap Q (laurent.op.map g)) (inputSchemeMap Q g) (coefficientMap_input Q g)

/-- The same original forward Laurent multiplication is preserved on the whole raw square. -/
theorem rawInputIso_unit (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    whiskerRight (boundedFlatPerfectTensorUnitPullbackAutomorphism (coefficientMap Q X)
        (ParameterLaurentUnit.projectedLaurentScalar Q X)).hom
        (boundedFlatPerfectPullback (inputSchemeMap Q (laurent.op.map g))) ≫
      (rawInputIso Q g).hom =
    (rawInputIso Q g).hom ≫ whiskerLeft (boundedFlatPerfectPullback (inputSchemeMap Q g))
      (boundedFlatPerfectTensorUnitPullbackAutomorphism (coefficientMap Q Y)
        (ParameterLaurentUnit.projectedLaurentScalar Q Y)).hom := by
  have h := tensorUnitRawInputIso_unit (coefficientMap Q X) (coefficientMap Q Y)
    (inputSchemeMap Q (laurent.op.map g)) (inputSchemeMap Q g) (coefficientMap_input Q g)
    (ParameterLaurentUnit.projectedLaurentScalar Q X)
  exact h.trans (congrArg
    (fun r : (Γ(scheme Q (laurent.op.obj Y), ⊤))ˣ =>
      (rawInputIso Q g).hom ≫ whiskerLeft (boundedFlatPerfectPullback (inputSchemeMap Q g))
        (boundedFlatPerfectTensorUnitPullbackAutomorphism (coefficientMap Q Y) r).hom)
    (ParameterLaurentUnit.projectedLaurentScalar_map Q g))

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
