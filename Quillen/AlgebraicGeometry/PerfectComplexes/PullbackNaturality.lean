/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.VectorBundlePullback


public import Aglib.CategoryTheory.ExactCategory.Functor
public import Quillen.AlgebraicGeometry.PerfectComplexes.Pullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.QuillenComparison
public import Quillen.AlgebraicGeometry.Scheme.Pullback
public import Quillen.CategoryTheory.SmallModel.CommonAmbientNaturality
public import Quillen.Waldhausen.QuillenComparison.ExactNaturality

/-!
# Naturality of the original vector-bundle/strict-perfect comparison

The actual degree-zero inclusion commutes with arbitrary geometric pullback.
The original S, small-model Q/S, and public K comparisons consequently commute
with the actual strict-perfect K-map in every connective degree, including zero.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex

open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Pretriangulated CochainComplex
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes

/-- Naturality of the original degree-zero S-construction comparison. -/
theorem vectorBundleSComparison_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (strictKPullback f n).comp (vectorBundleSComparison Y n) =
      (vectorBundleSComparison X n).comp
        (Waldhausen.KMap (AlgebraicGeometry.Scheme.Modules.vectorBundleExactPullback
          f).waldhausenExact n) := by
  unfold strictKPullback vectorBundleSComparison
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]
  exact Waldhausen.KMap_eq_of_iso _ _ (vectorBundleInclusionPullbackIso f) n

/-- The original small-model comparison commutes with arbitrary pullback. -/
theorem smallVectorBundleKMap_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.smallVectorBundleKMap X n).comp
      (AlgebraicGeometry.Scheme.pullbackK f n) =
      ((AlgebraicGeometry.Scheme.Modules.vectorBundleExactPullback f).KMap n).comp
        (AlgebraicGeometry.Scheme.Modules.smallVectorBundleKMap Y n) :=
  CategoryTheory.ExactCategory.ExactFunctor.smallModelToOriginal_commonAmbientKMap_naturality.{u +
    1, u}
    (AlgebraicGeometry.Scheme.Modules.vectorBundleExactPullback f) n

/-- The original public small-model/Q/S equivalence is natural on all schemes. -/
theorem vectorBundleQSEquiv_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (Waldhausen.KMap (AlgebraicGeometry.Scheme.Modules.vectorBundleExactPullback f).waldhausenExact
      n).comp
        (vectorBundleQSEquiv Y n).toMonoidHom =
      (vectorBundleQSEquiv X n).toMonoidHom.comp (AlgebraicGeometry.Scheme.pullbackK f n) := by
  apply MonoidHom.ext
  intro x
  apply (Waldhausen.QuillenComparison.comparisonKEquiv
    (AlgebraicGeometry.Scheme.Modules.vectorBundleExactStructure X) n).injective
  have hs := DFunLike.congr_fun (smallVectorBundleKMap_pullback f n) x
  have hq := DFunLike.congr_fun
    (Waldhausen.QuillenComparison.comparisonKEquiv_exactFunctor_naturality
      (AlgebraicGeometry.Scheme.Modules.vectorBundleExactPullback f) n) (vectorBundleQSEquiv Y n x)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hs hq ⊢
  simp only [vectorBundleQSEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at hq
  simpa only [vectorBundleQSEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    ← AlgebraicGeometry.Scheme.Modules.smallVectorBundleKEquiv_coe, MonoidHom.coe_coe]
      using hq.trans hs.symm

/-- The original public vector-bundle-to-strict comparison is natural for
arbitrary scheme morphisms, including in degree zero. -/
theorem vectorBundleToStrictKMap_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (strictKPullback f n).comp (vectorBundleToStrictKMap Y n) =
      (vectorBundleToStrictKMap X n).comp (AlgebraicGeometry.Scheme.pullbackK f n) := by
  unfold vectorBundleToStrictKMap
  rw [← MonoidHom.comp_assoc, vectorBundleSComparison_pullback,
    MonoidHom.comp_assoc, vectorBundleQSEquiv_pullback, MonoidHom.comp_assoc]

end Quillen.PerfectComplexes
