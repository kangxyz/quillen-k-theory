/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalSchemeLaurentTrack

/-!
# The original Laurent unit for scheme-parameter product families

The parameter coordinate on `(S × L) × Q` is pulled from `S × L`, and hence from
its original Laurent factor. Both parameter maps and maps of the fixed factor
preserve that exact unit. All products are over the integral terminal scheme.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Products AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
open Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
universe u
namespace Quillen.PerfectComplexes.ParameterLaurentUnit
open GlobalSectionChangeIndex GlobalSchemeLaurentTrack

private theorem pullbackUnit_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (v : (Γ(Z, ⊤))ˣ) :
    Units.map f.appTop.hom.toMonoidHom (Units.map g.appTop.hom.toMonoidHom v) =
      Units.map (f ≫ g).appTop.hom.toMonoidHom v := by
  ext
  simp

/-- The original parameter Laurent coordinate, pulled through the fixed-factor projection. -/
def projectedLaurentScalar (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    (Γ(((baseProductFunctor (toIntegerBase Q)).op.obj (laurent.op.obj X)).unop, ⊤))ˣ :=
  Units.map ((baseProductProjection (toIntegerBase Q)).app
    (laurent.op.obj X).unop).appTop.hom.toMonoidHom (laurentScalar X)

/-- Every actual parameter scheme map preserves the projected original Laurent coordinate. -/
theorem projectedLaurentScalar_map (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ}
    (g : X ⟶ Y) :
    Units.map (((baseProductFunctor (toIntegerBase Q)).op.map
      (laurent.op.map g)).unop).appTop.hom.toMonoidHom (projectedLaurentScalar Q X) =
      projectedLaurentScalar Q Y := by
  change Units.map ((baseProductFunctor (toIntegerBase Q)).map
    (laurent.map g.unop)).appTop.hom.toMonoidHom
      (Units.map ((baseProductProjection (toIntegerBase Q)).app
        (laurent.obj X.unop)).appTop.hom.toMonoidHom (laurentScalar X)) = _
  rw [pullbackUnit_comp, (baseProductProjection (toIntegerBase Q)).naturality]
  rw [← pullbackUnit_comp]
  exact congrArg (Units.map ((baseProductProjection (toIntegerBase Q)).app
    (laurent.obj Y.unop)).appTop.hom.toMonoidHom) (laurentScalar_map g)

/-- A map of the fixed factor preserves the parameter coordinate, including open restriction. -/
theorem projectedLaurentScalar_factor {P Q : Scheme.{u}} (f : P ⟶ Q)
    (X : Scheme.{u}ᵒᵖ) :
    Units.map ((baseProductTransformation (toIntegerBase P) (toIntegerBase Q)
      f (toIntegerBase_naturality f)).app (laurent.op.obj X).unop).appTop.hom.toMonoidHom
        (projectedLaurentScalar Q X) = projectedLaurentScalar P X := by
  unfold projectedLaurentScalar
  rw [pullbackUnit_comp, baseProductTransformation_projection]

/-- The actual evaluation-lifted identity unit on the parameter ambient Model. -/
def ambientUnit (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    𝟭 (globalModel.obj ((baseProductFunctor (toIntegerBase Q)).op.obj (laurent.op.obj X))) ≅
      𝟭 (globalModel.obj ((baseProductFunctor (toIntegerBase Q)).op.obj (laurent.op.obj X))) :=
  globalUnit _ (projectedLaurentScalar Q X)

/-- Original global reindexing preserves this same parameter unit for every scheme arrow. -/
theorem ambientUnit_naturality (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    Preserves (globalModel.map ((baseProductFunctor (toIntegerBase Q)).op.map
      (laurent.op.map g))).functor (ambientUnit Q X) (ambientUnit Q Y) :=
  globalUnit_reindex_of_eq _ _ _ (projectedLaurentScalar_map Q g)

/-- Actual pullback along the fixed-factor map preserves the original parameter unit. -/
theorem ambientUnit_factor {P Q : Scheme.{u}} (f : P ⟶ Q) (X : Scheme.{u}ᵒᵖ) :
    Preserves (globalModel.map ((baseProductTransformation (toIntegerBase P)
      (toIntegerBase Q) f (toIntegerBase_naturality f)).app
        (laurent.op.obj X).unop).op).functor (ambientUnit Q X) (ambientUnit P X) :=
  globalUnit_reindex_of_eq _ _ _ (projectedLaurentScalar_factor f X)

end Quillen.PerfectComplexes.ParameterLaurentUnit
