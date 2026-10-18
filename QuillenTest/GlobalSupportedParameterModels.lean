/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.GlobalOpenPairDiagram

/-! # Genuine scheme-parameter support, selected zeros and the original open factorization -/
@[expose] public section
noncomputable section
open CategoryTheory Opposite AlgebraicGeometry
open Quillen.PerfectComplexes.GlobalSectionChangeIndex
open Quillen.PerfectComplexes.GlobalSupportedParameter
universe u
namespace QuillenTest.GlobalSupportedParameterModels
variable {P Q S T : Scheme.{u}} (f : P ⟶ Q) [IsOpenImmersion f]

/-- A genuine parameter map preserves the original supported zero, with no flatness premise. -/
example (g : S ⟶ T) :
    (((ParameterModels.supported f).map g.op).functor.obj
      (((ParameterModels.supported f).obj (op T)).waldhausen.zero)) =
      ((ParameterModels.supported f).obj (op S)).waldhausen.zero :=
  ((ParameterModels.supported f).map g.op).zero

/-- Forgetting support commutes with every genuine parameter pullback. -/
example (g : S ⟶ T) :
    (ParameterModels.supported f).map g.op ≫ (ParameterModels.forget f).app (op S) =
      (ParameterModels.forget f).app (op T) ≫ (ParameterModels.ambient Q).map g.op :=
  (ParameterModels.forget f).naturality g.op

/-- Changing only the weak class and restricting retains the original global scheme map. -/
example (S : Scheme.{u}) :
    (ParameterModels.changeWeak f).app (op S) ≫
        (ParameterModels.openRestriction f).app (op S) =
      globalModel.map ((openTransformation f).app S).op :=
  congrArg (fun η => η.app
    (op (pair f S))) pairOpen_factor

end QuillenTest.GlobalSupportedParameterModels
