/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitSupportedCoefficientExact
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.TensorUnitCoefficientAutomorphism

/-!
# The original unit automorphism on the first coefficient tensor row

The coefficient automorphism acts as the identity on both original zero modules and as the
original multiplication map on the structure module. Applying the genuine coefficient tensor
functor gives an automorphism of the independently constructed tensor row. The whole row square
with the canonical one-step row retains both actual tensor-zero endpoint isomorphisms.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Complex
open Quillen.Waldhausen Quillen.Waldhausen.QuotientRows
open scoped Simplicial ZeroObject
universe u
namespace Quillen.PerfectComplexes
variable {U X : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι]


/-- Original coefficient multiplication lifted entrywise to the actual supported row. -/
def boundedFlatPerfectSupportedTensorUnitRowsAutomorphism (r : (Γ(X, ⊤))ˣ) :
    boundedFlatPerfectSupportedTensorUnitRows ι ≅ boundedFlatPerfectSupportedTensorUnitRows ι :=
  NatIso.ofComponents (fun K => NatIso.ofComponents
    (fun p => (boundedFlatPerfectSupported ι).isoMk
      (((complexTensorUnitRowsAutomorphism X r).app K.obj).app p))
    (by
      intro p q f
      apply (boundedFlatPerfectSupported ι).ι.map_injective
      exact ((complexTensorUnitRowsAutomorphism X r).hom.app K.obj).naturality f))
    (by
      intro K L f
      apply NatTrans.ext
      funext p
      apply (boundedFlatPerfectSupported ι).ι.map_injective
      exact NatTrans.congr_app ((complexTensorUnitRowsAutomorphism X r).hom.naturality f.hom) p)

/-- Inclusion retains every original tensor multiplication entry and complex degree. -/
theorem supportedTensorUnitRowsAutomorphism_original_f (r : (Γ(X, ⊤))ˣ)
    (K : (boundedFlatPerfectSupported ι).FullSubcategory) (p : Interval ⦋1⦌) (n : ℤ) :
    ((boundedFlatPerfectSupported ι).ι.map
      (((boundedFlatPerfectSupportedTensorUnitRowsAutomorphism ι r).hom.app K).app p)).f n =
      (moduleTensorCoefficientMap X ((tensorUnitCoefficientRowAutomorphism X r).hom.app p)).app
        (K.obj.X n) := rfl

/-- The genuine multiplication in the original supported quotient-row category. -/
def supportedTensorUnitFirstRowAutomorphism (r : (Γ(X, ⊤))ˣ) :
    boundedFlatPerfectSupportedTensorUnitFirstRow ι ≅
      boundedFlatPerfectSupportedTensorUnitFirstRow ι :=
  NatIso.ofComponents
    (fun K => (objects (boundedFlatPerfectSupportedWaldhausen ι) ⦋1⦌).isoMk
      ((boundedFlatPerfectSupportedTensorUnitRowsAutomorphism ι r).app K)) (by
      intro K L f
      apply ObjectProperty.hom_ext
      exact (boundedFlatPerfectSupportedTensorUnitRowsAutomorphism ι r).hom.naturality f)

/-- Forgetting only the row predicates keeps the original supported tensor multiplication. -/
theorem supportedTensorUnitFirstRowAutomorphism_original (r : (Γ(X, ⊤))ˣ)
    (K : (boundedFlatPerfectSupported ι).FullSubcategory) :
    ((supportedTensorUnitFirstRowAutomorphism ι r).hom.app K).hom =
      (boundedFlatPerfectSupportedTensorUnitRowsAutomorphism ι r).hom.app K := rfl

/-- The whole actual first-row unit square, with both tensor-zero endpoint isomorphisms. -/
theorem supportedTensorUnitFirstRowAutomorphism_comparison (r : (Γ(X, ⊤))ˣ) :
    (supportedTensorUnitFirstRowAutomorphism ι r).hom ≫ (supportedTensorUnitFirstRowIso ι).hom =
      (supportedTensorUnitFirstRowIso ι).hom ≫
        (Functor.isoWhiskerRight (boundedFlatPerfectSupportedTensorUnitAutomorphism ι r)
          (oneEmbedding (boundedFlatPerfectSupportedWaldhausen ι))).hom := by
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext p
  rcases p with ⟨⟨i, j⟩, hij⟩
  fin_cases i <;> fin_cases j <;> first
  | exact False.elim (Nat.not_succ_le_zero 0 hij)
  | exact (boundedFlatPerfectSupportedTensorUnitRows_zero ι K 0).eq_of_src _ _
  | exact (boundedFlatPerfectSupportedTensorUnitRows_zero ι K 1).eq_of_src _ _
  | change ((supportedTensorUnitFirstRowAutomorphism ι r).hom.app K).hom.app
        (interval 0 1 (by decide)) ≫ 𝟙 _ =
      𝟙 _ ≫ (boundedFlatPerfectSupportedTensorUnitAutomorphism ι r).hom.app K
    rw [supportedTensorUnitFirstRowAutomorphism_original]
    simp only [Category.comp_id, Category.id_comp]
    apply (boundedFlatPerfectSupported ι).ι.map_injective
    ext n : 1
    rw [supportedTensorUnitRowsAutomorphism_original_f,
      boundedFlatPerfectSupportedTensorUnitAutomorphism_hom_original,
      complexTensorUnitAutomorphism_hom_f]
    rfl

end Quillen.PerfectComplexes
