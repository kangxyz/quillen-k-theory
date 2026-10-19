/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientRow

/-!
# Mixed exactness of the actual first tensor row

The independently tensored coefficient row is lifted after proving its actual row predicates.
Its natural comparison with the original one-step embedding transports exactness, including the
all-triples relative cofibration tests and actual pushouts in the second input direction.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.Waldhausen Quillen.Waldhausen.QuotientRows
open scoped Simplicial
universe u
namespace Quillen.PerfectComplexes

/-- The genuine first tensor row as an object of the original quotient-row category. -/
def boundedFlatPerfectTensorUnitFirstRow (X : Scheme.{u}) :
    BoundedFlatPerfect X ⥤ Obj (boundedFlatPerfectWaldhausen X) ⦋1⦌ :=
  (objects (boundedFlatPerfectWaldhausen X) ⦋1⦌).lift
    (boundedFlatPerfectTensorUnitRows X) (boundedFlatPerfectTensorUnitRows_isRow X)

/-- The whole first-row comparison is natural in every actual second-input morphism. -/
def tensorUnitFirstRowIso (X : Scheme.{u}) :
    boundedFlatPerfectTensorUnitFirstRow X ≅
      boundedFlatPerfectTensorUnit X ⋙ oneEmbedding (boundedFlatPerfectWaldhausen X) :=
  NatIso.ofComponents
    (fun K => (objects (boundedFlatPerfectWaldhausen X) ⦋1⦌).isoMk
      (tensorUnitRowDiagramIso X K)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext p
      rcases p with ⟨⟨i, j⟩, hij⟩
      fin_cases i <;> fin_cases j <;> solve
      | exact False.elim (Nat.not_succ_le_zero 0 hij)
      | exact (boundedFlatPerfectTensorUnitRows_zero X K 0).eq_of_src _ _
      | exact (boundedFlatPerfectTensorUnitRows_zero X K 1).eq_of_src _ _
      | change (boundedFlatPerfectTensorUnit X).map f ≫ 𝟙 _ =
          𝟙 _ ≫ (boundedFlatPerfectTensorUnit X).map f
        simp)

/-- The actual first-row tensor functor satisfies every original exactness condition. -/
theorem boundedFlatPerfectTensorUnitFirstRow_exact (X : Scheme.{u}) :
    IsExact (boundedFlatPerfectWaldhausen X).cof (boundedFlatPerfectWaldhausen X).weq
      (waldhausenStructure (boundedFlatPerfectWaldhausen X) ⦋1⦌).cof
      (waldhausenStructure (boundedFlatPerfectWaldhausen X) ⦋1⦌).weq
      (boundedFlatPerfectTensorUnitFirstRow X) :=
  ((boundedFlatPerfectTensorUnit_exact X).comp
    (oneEmbedding_exact (boundedFlatPerfectWaldhausen X))).of_iso (tensorUnitFirstRowIso X).symm

/-- The mixed first-row/second-input square has the genuine relative pushout cofibration. -/
theorem tensorUnitFirstRow_relative_cof (X : Scheme.{u}) {K L : BoundedFlatPerfect X}
    (f : K ⟶ L) (hf : (boundedFlatPerfectWaldhausen X).cof f)
    (i j k : Fin 2) (hij : i ≤ j) (hjk : j ≤ k) :
    (boundedFlatPerfectWaldhausen X).cof
      (ExtensionCategory.relativeMap (boundedFlatPerfectWaldhausen X)
        ((horizontalArrow (boundedFlatPerfectWaldhausen X) i j k hij hjk).map
          ((boundedFlatPerfectTensorUnitFirstRow X).map f))) :=
  ((boundedFlatPerfectTensorUnitFirstRow_exact X).cofibration f hf i j k hij hjk).2

/-- Tensoring any second-input quotient/nerve grid produces a genuine grid of first rows. -/
theorem tensorUnitFirstRow_grid (X : Scheme.{u}) {n m : SimplexCategory}
    (A : Grid₂ n m ⥤ BoundedFlatPerfect X)
    (hA : IsSimplex₂ (boundedFlatPerfectWaldhausen X).cof
      (boundedFlatPerfectWaldhausen X).weq A) :
    IsSimplex₂ (waldhausenStructure (boundedFlatPerfectWaldhausen X) ⦋1⦌).cof
      (waldhausenStructure (boundedFlatPerfectWaldhausen X) ⦋1⦌).weq
      (A ⋙ boundedFlatPerfectTensorUnitFirstRow X) :=
  hA.postcomp _ _ (boundedFlatPerfectTensorUnitFirstRow_exact X)

/-- Every actual second-input pushout is carried to a pushout of the original tensor rows. -/
theorem tensorUnitFirstRow_pushout (X : Scheme.{u}) {A B C D : BoundedFlatPerfect X}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (hf : (boundedFlatPerfectWaldhausen X).cof f) (h : IsPushout f g i j) :
    IsPushout ((boundedFlatPerfectTensorUnitFirstRow X).map f)
      ((boundedFlatPerfectTensorUnitFirstRow X).map g)
      ((boundedFlatPerfectTensorUnitFirstRow X).map i)
      ((boundedFlatPerfectTensorUnitFirstRow X).map j) :=
  (boundedFlatPerfectTensorUnitFirstRow_exact X).pushout hf h

end Quillen.PerfectComplexes
