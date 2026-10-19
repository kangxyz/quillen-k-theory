/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.SupportedTensorInputModelCube

/-! # Original supported inputs through the complete tensor-forgetting cube

The forward and reverse component routes retain all four independently specified pair arrows,
their original commutative square, the selected zero transports and the actual supported input.
-/
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open Quillen.PerfectComplexes.SupportedTensorEvaluation
universe u
namespace QuillenTest.SupportedTensorInputCube

variable {A B C D : Scheme.OpenPairs.{u}}
  (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)
  (K : (modelOf (boundedFlatPerfectSupportedWaldhausen B.obj.hom)).category)

/-- An original supported input follows the same complete forward route on either side. -/
theorem original_supported_input :
    (isoWhiskerRight (tensorSupportedRawModelInputIso p q a b h)
      (tensorCoefficientSupportedForgetModel C.obj.hom).functor).hom.app K ≫
        (modelInputForgetRightRoute q b).hom.app K =
      (modelInputForgetLeftRoute p a).hom.app K ≫
        (isoWhiskerLeft (tensorCoefficientSupportedForgetModel B.obj.hom).functor
          (tensorUnitRawModelInputIso p.hom.right q.hom.right a.hom.right b.hom.right
            (congrArg (fun f : C ⟶ B => f.hom.right) h))).hom.app K :=
  NatTrans.congr_app (congrArg Iso.hom (tensorSupportedModelInputForgetCube p q a b h)) K

/-- The genuine inverse paths also agree, without choosing another normalization. -/
theorem original_supported_inverse_route :
    (modelInputForgetRightRoute q b).inv.app K ≫
        (isoWhiskerRight (tensorSupportedRawModelInputIso p q a b h)
          (tensorCoefficientSupportedForgetModel C.obj.hom).functor).inv.app K =
      (isoWhiskerLeft (tensorCoefficientSupportedForgetModel B.obj.hom).functor
        (tensorUnitRawModelInputIso p.hom.right q.hom.right a.hom.right b.hom.right
          (congrArg (fun f : C ⟶ B => f.hom.right) h))).inv.app K ≫
        (modelInputForgetLeftRoute p a).inv.app K :=
  NatTrans.congr_app (congrArg Iso.inv (tensorSupportedModelInputForgetCube p q a b h)) K

end QuillenTest.SupportedTensorInputCube
