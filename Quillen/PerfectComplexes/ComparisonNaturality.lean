/-
Copyright (c) 2026 Quillen K-Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-Theory contributors
-/
import Quillen.PerfectComplexes.QuillenComparison
import Quillen.PerfectComplexes.RestrictionFunctoriality
import Quillen.CategoryTheory.SmallModel.CommonAmbientNaturality
import Quillen.Waldhausen.QuillenComparison.ExactNaturality

/-!
# Naturality of the original vector-bundle/perfect-complex comparisons

The actual degree-zero inclusion commutes with open restriction by the
single-complex/termwise-restriction isomorphism. The original public scheme
K comparison is natural by the proved small-model and Q/S squares. Thus both
canonical public K-to-strict and K-to-locally-perfect homomorphisms commute
with open restriction in every connective degree, including degree zero.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

/-- The degree-zero inclusion commutes with genuine termwise restriction. -/
def vectorBundleInclusionRestrictIso {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] :
    vectorBundleInclusion X ⋙ strictRestrict j ≅
      SchemeSheaf.vectorBundleRestrict j ⋙ vectorBundleInclusion U :=
  Functor.fullyFaithfulCancelRight (strictPerfect U).ι
    (Functor.isoWhiskerLeft (SchemeSheaf.finiteLocallyFree X).ι
      (HomologicalComplex.singleMapHomologicalComplex
        (Scheme.Modules.restrictFunctor j) (ComplexShape.up ℤ) 0))

/-- Naturality of the original degree-zero S-construction comparison. -/
theorem vectorBundleSComparison_restrict {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (strictKRestrict j n).comp (vectorBundleSComparison X n) =
      (vectorBundleSComparison U n).comp
        (Waldhausen.KMap (SchemeSheaf.vectorBundleExactRestrict j).waldhausenExact n) := by
  unfold strictKRestrict vectorBundleSComparison
  rw [← Waldhausen.KMap_comp, ← Waldhausen.KMap_comp]
  exact Waldhausen.KMap_eq_of_iso _ _ (vectorBundleInclusionRestrictIso j) n

/-- The original small-model comparison commutes with open restriction. -/
theorem smallVectorBundleKMap_restrict {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (SchemeSheaf.smallVectorBundleKMap U n).comp (Quillen.Scheme.restrictK j n) =
      ((SchemeSheaf.vectorBundleExactRestrict j).KMap n).comp
        (SchemeSheaf.smallVectorBundleKMap X n) :=
  Quillen.ExactFunctor.smallModelToOriginal_commonAmbientKMap_naturality.{u + 1, u}
    (SchemeSheaf.vectorBundleExactRestrict j) n

/-- Naturality of the actual public small-model/Q/S equivalence. -/
theorem vectorBundleQSEquiv_restrict {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (Waldhausen.KMap (SchemeSheaf.vectorBundleExactRestrict j).waldhausenExact n).comp
        (vectorBundleQSEquiv X n).toMonoidHom =
      (vectorBundleQSEquiv U n).toMonoidHom.comp (Quillen.Scheme.restrictK j n) := by
  apply MonoidHom.ext
  intro x
  apply (Waldhausen.QuillenComparison.comparisonKEquiv
    (SchemeSheaf.vectorBundleExactStructure U) n).injective
  have hs := DFunLike.congr_fun (smallVectorBundleKMap_restrict j n) x
  have hq := DFunLike.congr_fun
    (Waldhausen.QuillenComparison.comparisonKEquiv_exactFunctor_naturality
      (SchemeSheaf.vectorBundleExactRestrict j) n) (vectorBundleQSEquiv X n x)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hs hq ⊢
  simp only [vectorBundleQSEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at hq
  simpa only [vectorBundleQSEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    ← SchemeSheaf.smallVectorBundleKEquiv_toMonoidHom, MulEquiv.coe_toMonoidHom]
      using hq.trans hs.symm

/-- The original public vector-bundle-to-strict comparison is natural. -/
theorem vectorBundleToStrictKMap_restrict {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (strictKRestrict j n).comp (vectorBundleToStrictKMap X n) =
      (vectorBundleToStrictKMap U n).comp (Quillen.Scheme.restrictK j n) := by
  unfold vectorBundleToStrictKMap
  rw [← MonoidHom.comp_assoc, vectorBundleSComparison_restrict,
    MonoidHom.comp_assoc, vectorBundleQSEquiv_restrict, MonoidHom.comp_assoc]

/-- The original public vector-bundle-to-local comparison is natural. -/
theorem vectorBundleToPerfectKMap_restrict {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] (n : ℕ) :
    (perfectKRestrict j n).comp (vectorBundleToPerfectKMap X n) =
      (vectorBundleToPerfectKMap U n).comp (Quillen.Scheme.restrictK j n) := by
  rw [← strictToPerfect_comp_vectorBundleToStrictKMap,
    ← strictToPerfect_comp_vectorBundleToStrictKMap,
    ← MonoidHom.comp_assoc, strictToPerfectKMap_restrict,
    MonoidHom.comp_assoc, vectorBundleToStrictKMap_restrict, MonoidHom.comp_assoc]

end Quillen.PerfectComplexes
