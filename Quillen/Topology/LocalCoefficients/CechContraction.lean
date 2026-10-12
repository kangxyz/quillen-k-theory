/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.LocalCoefficients.CechChains

/-!
# Contraction of the actual augmented Čech rows

The chosen containing member is inserted explicitly into the label list.
The identities below prove a genuine extra degeneracy, which constructs a
chain homotopy equivalence from each actual Čech row to its original
small-chain module concentrated in degree zero.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits Opposite
open scoped Simplicial

universe u

namespace Quillen.LocalCoefficients

variable {X : Type u} [TopologicalSpace X] {ι : Type u}
  (U : ι → Set X) (A : System.{u, u} X) (n : SimplexCategory)

/-- Insertion of the chosen label satisfies all extra-degeneracy identities. -/
def cechRowExtraDegeneracy : (cechAugmentedRow U A n).ExtraDegeneracy where
  s' := cechAugmentationSection U A n
  s := cechExtraDegeneracyMap U A n
  s'_comp_ε := by
    apply Sigma.hom_ext
    intro σ
    simp [cechAugmentedRow, cechAugmentationSection, cechModuleAugmentation,
      cechChainInclusion, smallChainInclusion, smallChainModule]
  s₀_comp_δ₁ := by
    apply Sigma.hom_ext
    rintro ⟨σ, l⟩
    simp only [Nat.reduceAdd, cechAugmentedRow, cechSimplicialModule, cechChainMap,
      restrictCechSimplex, cechChainInclusion, Functor.id_obj, cechModuleAugmentation,
      smallChainInclusion, cechExtraDegeneracyMap, SimplicialObject.δ, SimplexCategory.δ,
      SimplexCategory.mkHom, Fin.isValue, Quiver.Hom.unop_op,
      SimplexCategory.Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
      Fin.succAboveOrderEmb_apply, colimit.ι_desc_assoc, Discrete.functor_obj_eq_as,
      Cofan.mk_pt, Cofan.mk_ι_app, colimit.ι_desc, cechAugmentationSection]
    congr 1
    apply congrArg (Sigma.mk σ)
    funext i
    fin_cases i
    rfl
  s_comp_δ₀ p := by
    apply Sigma.hom_ext
    rintro ⟨σ, l⟩
    simp only [cechAugmentedRow, cechSimplicialModule, cechChainModule, cechChainMap,
      restrictCechSimplex, cechChainInclusion, Functor.id_obj, cechExtraDegeneracyMap,
      SimplicialObject.δ, SimplexCategory.δ, SimplexCategory.mkHom, Quiver.Hom.unop_op,
      SimplexCategory.Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
      Fin.succAboveOrderEmb_apply, Fin.zero_succAbove, colimit.ι_desc_assoc,
      Discrete.functor_obj_eq_as, Cofan.mk_pt, Cofan.mk_ι_app, colimit.ι_desc,
      Category.comp_id]
    congr 1
  s_comp_δ p i := by
    apply Sigma.hom_ext
    rintro ⟨σ, l⟩
    simp only [cechAugmentedRow, cechSimplicialModule, cechChainMap, restrictCechSimplex,
      cechChainInclusion, Functor.id_obj, cechExtraDegeneracyMap, SimplicialObject.δ,
      SimplexCategory.δ, SimplexCategory.mkHom, Quiver.Hom.unop_op,
      SimplexCategory.Hom.toOrderHom_mk, OrderEmbedding.toOrderHom_coe,
      Fin.succAboveOrderEmb_apply, colimit.ι_desc_assoc, Discrete.functor_obj_eq_as,
      Cofan.mk_pt, Cofan.mk_ι_app, colimit.ι_desc]
    congr 1
    apply congrArg (Sigma.mk σ)
    funext j
    refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp
  s_comp_σ p i := by
    apply Sigma.hom_ext
    rintro ⟨σ, l⟩
    simp only [cechAugmentedRow, cechSimplicialModule, cechChainMap, restrictCechSimplex,
      cechChainInclusion, Functor.id_obj, cechExtraDegeneracyMap, SimplicialObject.σ,
      SimplexCategory.σ, SimplexCategory.mkHom, Quiver.Hom.unop_op,
      SimplexCategory.Hom.toOrderHom_mk, Fin.predAboveOrderHom_coe, colimit.ι_desc_assoc,
      Discrete.functor_obj_eq_as, Cofan.mk_pt, Cofan.mk_ι_app, colimit.ι_desc]
    congr 1
    apply congrArg (Sigma.mk σ)
    funext j
    refine Fin.cases ?_ (fun j ↦ ?_) j <;> simp

/-- The genuine alternating Čech row complex in fixed singular degree. -/
def cechRowComplex : ChainComplex (ModuleCat.{u} ℤ) ℕ :=
  (AlgebraicTopology.alternatingFaceMapComplex _).obj (cechSimplicialModule U A n)

/-- Its original augmentation to the original small-chain module in degree zero. -/
def cechRowAugmentation : cechRowComplex U A n ⟶
    (ChainComplex.single₀ (ModuleCat.{u} ℤ)).obj (smallChainModule U A n) :=
  AlgebraicTopology.AlternatingFaceMapComplex.ε.app (cechAugmentedRow U A n)

/-- An actual chain homotopy equivalence, constructed from the proved insertion identities. -/
def cechRowHomotopyEquiv : HomotopyEquiv (cechRowComplex U A n)
    ((ChainComplex.single₀ (ModuleCat.{u} ℤ)).obj (smallChainModule U A n)) :=
  (cechRowExtraDegeneracy U A n).homotopyEquiv

@[simp]
theorem cechRowHomotopyEquiv_hom :
    (cechRowHomotopyEquiv U A n).hom = cechRowAugmentation U A n := rfl

/-- The original augmented Čech row is a quasi-isomorphism for arbitrary local coefficients. -/
theorem cechRowAugmentation_quasiIso : QuasiIso (cechRowAugmentation U A n) :=
  inferInstanceAs (QuasiIso (cechRowHomotopyEquiv U A n).hom)

end Quillen.LocalCoefficients
