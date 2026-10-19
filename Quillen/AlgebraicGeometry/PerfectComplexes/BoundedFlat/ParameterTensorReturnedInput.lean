/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.ParameterTensorReturnedCell

/-! # Actual coefficient input for the returned genuine tensor

The specified evaluation/unit comparisons transport the original strict coefficient square.
The whole original tensor multiplication is preserved, with no additional compatibility input.
Forward evaluation of this square still has its separate raw tensor pseudonaturality comparison.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.FunctorIdentityAutomorphism
open AlgebraicGeometry.Scheme.PolynomialLaurent.GlobalIndex
universe u w
namespace Quillen.PerfectComplexes.ParameterTensorEvaluationRow
open GlobalSectionChangeIndex Quillen.KTheory.Bass.GeometricSeedCospan

/-- The original strict coefficient square, displayed at the actual category functors. -/
def coefficientFunctorSquare (M : Scheme.{u}ᵒᵖ ⥤ Model.{w})
    {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    (M.map (coefficient.app X)).functor ⋙ (M.map (laurent.op.map g)).functor ≅
      (M.map g).functor ⋙ (M.map (coefficient.app Y)).functor :=
  eqToIso (congrArg (fun k : M.obj X ⟶ M.obj (laurent.op.obj Y) => k.functor)
    ((M.map_comp (coefficient.app X) (laurent.op.map g)).symm.trans
      ((congrArg M.map (coefficient.naturality g).symm).trans
        (M.map_comp g (coefficient.app Y)))))

/-- The actual return iso identifies the transported multiplication with the same original scalar.
-/
theorem returnedTensorUnit_scalar (Q : Scheme.{u}) (X : Scheme.{u}ᵒᵖ) :
    returnedTensorUnit Q X =
      (onFunctor (returnedTensorModel Q X).functor (ParameterLaurentUnit.ambientUnit Q X)).hom := by
  apply NatTrans.ext
  funext K
  apply (cancel_epi ((returnedTensorIso Q X).hom.app K)).mp
  have h := NatTrans.congr_app (returnedTensorIso_unit Q X) K
  simp only [NatTrans.comp_app, onFunctor_hom_app] at h ⊢
  exact h.symm.trans
    (by simpa only [Functor.id_map, Functor.id_obj, ParameterLaurentUnit.ambientUnit,
        scheme] using
      ((ParameterLaurentUnit.ambientUnit Q X).hom.naturality
        ((returnedTensorIso Q X).hom.app K)).symm)

/-- The original coefficient square with its specified genuine return comparisons on both sides.
-/
def returnedInputIso (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    (returnedTensorModel Q X).functor ⋙
        ((ParameterModels.ambient Q).map (laurent.op.map g)).functor ≅
      ((ParameterModels.ambient Q).map g).functor ⋙ (returnedTensorModel Q Y).functor :=
  isoWhiskerRight (returnedTensorIso Q X).symm
      ((ParameterModels.ambient Q).map (laurent.op.map g)).functor ≪≫
    coefficientFunctorSquare (ParameterModels.ambient Q) g ≪≫
      isoWhiskerLeft ((ParameterModels.ambient Q).map g).functor (returnedTensorIso Q Y)

/-- The entire genuine multiplication respects this actual coefficient-input square. -/
theorem returnedInputIso_unit (Q : Scheme.{u}) {X Y : Scheme.{u}ᵒᵖ} (g : X ⟶ Y) :
    whiskerRight (returnedTensorUnit Q X)
        ((ParameterModels.ambient Q).map (laurent.op.map g)).functor ≫
      (returnedInputIso Q g).hom =
    (returnedInputIso Q g).hom ≫
      whiskerLeft ((ParameterModels.ambient Q).map g).functor (returnedTensorUnit Q Y) := by
  rw [returnedTensorUnit_scalar, returnedTensorUnit_scalar]
  exact onFunctor_whisker_square _ _ _ _ (returnedInputIso Q g).hom
    (ParameterLaurentUnit.ambientUnit Q X) (ParameterLaurentUnit.ambientUnit Q Y)
    (ParameterLaurentUnit.ambientUnit_naturality Q g).whisker

end Quillen.PerfectComplexes.ParameterTensorEvaluationRow
