/-
Copyright (c) 2026 Quillen K-Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.VectorBundleRestriction


public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.AlgebraicGeometry.PerfectComplexes.QuillenComparison
public import Quillen.AlgebraicGeometry.PerfectComplexes.RestrictionFunctoriality
public import Quillen.CategoryTheory.SmallModel.CommonAmbientNaturality
public import Quillen.Waldhausen.QuillenComparison.ExactNaturality

/-!
# Naturality of the original vector-bundle/perfect-complex comparisons

The actual degree-zero inclusion commutes with open restriction by the
single-complex/termwise-restriction isomorphism. The original public scheme
K comparison is natural by the proved small-model and Q/S squares. Thus both
canonical public K-to-strict and K-to-locally-perfect homomorphisms commute
with open restriction in every connective degree, including degree zero.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

/-- Naturality of the original degree-zero S-construction comparison. -/
theorem vectorBundleSComparison_restrict {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (strictKRestrict j n).comp (vectorBundleSComparison X n) =
      (vectorBundleSComparison U n).comp
        (Waldhausen.KMap (AlgebraicGeometry.Scheme.Modules.vectorBundleExactRestrict
          j).waldhausenExact n) := by
  unfold strictKRestrict vectorBundleSComparison
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]
  exact Waldhausen.KMap_eq_of_iso _ _ (vectorBundleInclusionRestrictIso j) n

/-- The original small-model comparison commutes with open restriction. -/
theorem smallVectorBundleKMap_restrict {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.smallVectorBundleKMap U n).comp
      (AlgebraicGeometry.Scheme.restrictK j n) =
      ((AlgebraicGeometry.Scheme.Modules.vectorBundleExactRestrict j).KMap n).comp
        (AlgebraicGeometry.Scheme.Modules.smallVectorBundleKMap X n) :=
  CategoryTheory.ExactCategory.ExactFunctor.smallModelToOriginal_commonAmbientKMap_naturality.{u +
    1, u}
    (AlgebraicGeometry.Scheme.Modules.vectorBundleExactRestrict j) n

/-- Naturality of the actual public small-model/Q/S equivalence. -/
theorem vectorBundleQSEquiv_restrict {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (Waldhausen.KMap (AlgebraicGeometry.Scheme.Modules.vectorBundleExactRestrict j).waldhausenExact
      n).comp
        (vectorBundleQSEquiv X n).toMonoidHom =
      (vectorBundleQSEquiv U n).toMonoidHom.comp (AlgebraicGeometry.Scheme.restrictK j n) := by
  apply MonoidHom.ext
  intro x
  apply (Waldhausen.QuillenComparison.comparisonKEquiv
    (AlgebraicGeometry.Scheme.Modules.vectorBundleExactStructure U) n).injective
  have hs := DFunLike.congr_fun (smallVectorBundleKMap_restrict j n) x
  have hq := DFunLike.congr_fun
    (Waldhausen.QuillenComparison.comparisonKEquiv_exactFunctor_naturality
      (AlgebraicGeometry.Scheme.Modules.vectorBundleExactRestrict j) n) (vectorBundleQSEquiv X n x)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hs hq ⊢
  simp only [vectorBundleQSEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at hq
  simpa only [vectorBundleQSEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    ← AlgebraicGeometry.Scheme.Modules.smallVectorBundleKEquiv_coe, MonoidHom.coe_coe]
      using hq.trans hs.symm

/-- The original public vector-bundle-to-strict comparison is natural. -/
theorem vectorBundleToStrictKMap_restrict {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (strictKRestrict j n).comp (vectorBundleToStrictKMap X n) =
      (vectorBundleToStrictKMap U n).comp (AlgebraicGeometry.Scheme.restrictK j n) := by
  unfold vectorBundleToStrictKMap
  rw [← MonoidHom.comp_assoc, vectorBundleSComparison_restrict,
    MonoidHom.comp_assoc, vectorBundleQSEquiv_restrict, MonoidHom.comp_assoc]

/-- The original public vector-bundle-to-local comparison is natural. -/
theorem vectorBundleToPerfectKMap_restrict {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (perfectKRestrict j n).comp (vectorBundleToPerfectKMap X n) =
      (vectorBundleToPerfectKMap U n).comp (AlgebraicGeometry.Scheme.restrictK j n) := by
  rw [← strictToPerfect_comp_vectorBundleToStrictKMap,
    ← strictToPerfect_comp_vectorBundleToStrictKMap,
    ← MonoidHom.comp_assoc, strictToPerfectKMap_restrict,
    MonoidHom.comp_assoc, vectorBundleToStrictKMap_restrict, MonoidHom.comp_assoc]

end Quillen.PerfectComplexes
