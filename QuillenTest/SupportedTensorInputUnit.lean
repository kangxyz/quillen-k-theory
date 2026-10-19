/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedModelInputUnit

/-! # Original supported tensor multiplication at every actual input object -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.IteratedS Quillen.PerfectComplexes
open Quillen.PerfectComplexes.SupportedTensorEvaluation
universe u
namespace QuillenTest.SupportedTensorInputUnit

/-- The genuine forward multiplication follows both complete original Model input routes. -/
theorem original_multiplication_square {A B C D : Scheme.OpenPairs.{u}}
    (p : A ⟶ B) (q : C ⟶ D) (a : C ⟶ A) (b : D ⟶ B) (h : a ≫ p = q ≫ b)
    (r : (Γ(A.obj.right, ⊤))ˣ)
    (K : (modelOf (boundedFlatPerfectSupportedWaldhausen B.obj.hom)).category) :
    (evaluationRawMap a).functor.map ((tensorSupportedPairModelTransformation p r).app K) ≫
        (tensorSupportedRawModelInputIso p q a b h).hom.app K =
      (tensorSupportedRawModelInputIso p q a b h).hom.app K ≫
        (tensorSupportedPairModelTransformation q
          (Units.map a.hom.right.appTop.hom.toMonoidHom r)).app
            ((evaluationRawMap b).functor.obj K) :=
  NatTrans.congr_app (modelInputIso_unit p q a b h r) K

end QuillenTest.SupportedTensorInputUnit
