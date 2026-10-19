/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import
  Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedCoefficientRow

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
variable {U X : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι]

/-- The genuine first tensor row as an object of the original quotient-row category. -/
def boundedFlatPerfectSupportedTensorUnitFirstRow :
    (boundedFlatPerfectSupported ι).FullSubcategory ⥤
      Obj (boundedFlatPerfectSupportedWaldhausen ι) ⦋1⦌ :=
  (objects (boundedFlatPerfectSupportedWaldhausen ι) ⦋1⦌).lift
    (boundedFlatPerfectSupportedTensorUnitRows ι)
    (boundedFlatPerfectSupportedTensorUnitRows_isRow ι)

/-- The whole first-row comparison is natural in every actual second-input morphism. -/
def supportedTensorUnitFirstRowIso :
    boundedFlatPerfectSupportedTensorUnitFirstRow ι ≅
      boundedFlatPerfectSupportedTensorUnit ι ⋙
        oneEmbedding (boundedFlatPerfectSupportedWaldhausen ι) :=
  NatIso.ofComponents
    (fun K => (objects (boundedFlatPerfectSupportedWaldhausen ι) ⦋1⦌).isoMk
      (supportedTensorUnitRowDiagramIso ι K)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext p
      rcases p with ⟨⟨i, j⟩, hij⟩
      fin_cases i <;> fin_cases j <;> solve
      | exact False.elim (Nat.not_succ_le_zero 0 hij)
      | exact (boundedFlatPerfectSupportedTensorUnitRows_zero ι K 0).eq_of_src _ _
      | exact (boundedFlatPerfectSupportedTensorUnitRows_zero ι K 1).eq_of_src _ _
      | change (boundedFlatPerfectSupportedTensorUnit ι).map f ≫ 𝟙 _ =
          𝟙 _ ≫ (boundedFlatPerfectSupportedTensorUnit ι).map f
        simp)

/-- The actual first-row tensor functor satisfies every original exactness condition. -/
theorem boundedFlatPerfectSupportedTensorUnitFirstRow_exact :
    IsExact (boundedFlatPerfectSupportedWaldhausen ι).cof
      (boundedFlatPerfectSupportedWaldhausen ι).weq
      (waldhausenStructure (boundedFlatPerfectSupportedWaldhausen ι) ⦋1⦌).cof
      (waldhausenStructure (boundedFlatPerfectSupportedWaldhausen ι) ⦋1⦌).weq
      (boundedFlatPerfectSupportedTensorUnitFirstRow ι) :=
  ((boundedFlatPerfectSupportedTensorUnit_exact ι).comp
    (oneEmbedding_exact (boundedFlatPerfectSupportedWaldhausen ι))).of_iso
      (supportedTensorUnitFirstRowIso ι).symm

/-- The mixed first-row/second-input square has the genuine relative pushout cofibration. -/
theorem supportedTensorUnitFirstRow_relative_cof
    {K L : (boundedFlatPerfectSupported ι).FullSubcategory}
    (f : K ⟶ L) (hf : (boundedFlatPerfectSupportedWaldhausen ι).cof f)
    (i j k : Fin 2) (hij : i ≤ j) (hjk : j ≤ k) :
    (boundedFlatPerfectSupportedWaldhausen ι).cof
      (ExtensionCategory.relativeMap (boundedFlatPerfectSupportedWaldhausen ι)
        ((horizontalArrow (boundedFlatPerfectSupportedWaldhausen ι) i j k hij hjk).map
          ((boundedFlatPerfectSupportedTensorUnitFirstRow ι).map f))) :=
  ((boundedFlatPerfectSupportedTensorUnitFirstRow_exact ι).cofibration f hf i j k hij hjk).2

/-- Tensoring any second-input quotient/nerve grid produces a genuine grid of first rows. -/
theorem supportedTensorUnitFirstRow_grid {n m : SimplexCategory}
    (A : Grid₂ n m ⥤ (boundedFlatPerfectSupported ι).FullSubcategory)
    (hA : IsSimplex₂ (boundedFlatPerfectSupportedWaldhausen ι).cof
      (boundedFlatPerfectSupportedWaldhausen ι).weq A) :
    IsSimplex₂ (waldhausenStructure (boundedFlatPerfectSupportedWaldhausen ι) ⦋1⦌).cof
      (waldhausenStructure (boundedFlatPerfectSupportedWaldhausen ι) ⦋1⦌).weq
      (A ⋙ boundedFlatPerfectSupportedTensorUnitFirstRow ι) :=
  hA.postcomp _ _ (boundedFlatPerfectSupportedTensorUnitFirstRow_exact ι)

/-- Every actual second-input pushout is carried to a pushout of the original tensor rows. -/
theorem supportedTensorUnitFirstRow_pushout
    {A B C D : (boundedFlatPerfectSupported ι).FullSubcategory}
    {f : A ⟶ B} {g : A ⟶ C} {i : B ⟶ D} {j : C ⟶ D}
    (hf : (boundedFlatPerfectSupportedWaldhausen ι).cof f) (h : IsPushout f g i j) :
    IsPushout ((boundedFlatPerfectSupportedTensorUnitFirstRow ι).map f)
      ((boundedFlatPerfectSupportedTensorUnitFirstRow ι).map g)
      ((boundedFlatPerfectSupportedTensorUnitFirstRow ι).map i)
      ((boundedFlatPerfectSupportedTensorUnitFirstRow ι).map j) :=
  (boundedFlatPerfectSupportedTensorUnitFirstRow_exact ι).pushout hf h

end Quillen.PerfectComplexes
