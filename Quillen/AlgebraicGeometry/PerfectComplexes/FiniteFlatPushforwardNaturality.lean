/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.FiniteFlatPushforward
public import Quillen.AlgebraicGeometry.PerfectComplexes.QuillenComparison
public import Quillen.AlgebraicGeometry.Scheme.FiniteFlatPushforward
public import Quillen.CategoryTheory.SmallModel.CommonAmbientNaturality
public import Quillen.Waldhausen.QuillenComparison.ExactNaturality
public import Quillen.Waldhausen.Functoriality.KMap

/-!
# Naturality of the original vector-bundle/strict-perfect comparison

The actual degree-zero inclusion commutes with finite flat geometric direct image.
The original S, small-model Q/S, and public K comparisons consequently commute
with the actual strict-perfect direct-image K-map in every connective degree, including zero.
-/
@[expose] public section

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
theorem vectorBundleSComparison_finiteFlatPushforward {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f] [Flat f] (n : ℕ) :
    (strictKFiniteFlatPushforward f n).comp (vectorBundleSComparison X n) =
      (vectorBundleSComparison Y n).comp
        (Waldhausen.KMap (AlgebraicGeometry.Scheme.Modules.vectorBundlePushforwardExact
          f).waldhausenExact n) := by
  unfold strictKFiniteFlatPushforward vectorBundleSComparison
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]
  exact Waldhausen.KMap_eq_of_iso _ _ (vectorBundleInclusionFiniteFlatPushforwardIso f) n

/-- The original small-model comparison commutes with finite flat direct image. -/
theorem smallVectorBundleKMap_finiteFlatPushforward {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f] [Flat f] (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.smallVectorBundleKMap Y n).comp
      (AlgebraicGeometry.Scheme.Modules.schemeKPushforward f n) =
      ((AlgebraicGeometry.Scheme.Modules.vectorBundlePushforwardExact f).KMap n).comp
        (AlgebraicGeometry.Scheme.Modules.smallVectorBundleKMap X n) :=
  ExactFunctor.smallModelToOriginal_commonAmbientKMap_naturality.{u + 1, u}
    (AlgebraicGeometry.Scheme.Modules.vectorBundlePushforwardExact f) n

/-- The original small-model/Q/S equivalence commutes with finite flat direct image. -/
theorem vectorBundleQSEquiv_finiteFlatPushforward {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f] [Flat f] (n : ℕ) :
    (Waldhausen.KMap (AlgebraicGeometry.Scheme.Modules.vectorBundlePushforwardExact
      f).waldhausenExact n).comp
        (vectorBundleQSEquiv X n).toMonoidHom =
      (vectorBundleQSEquiv Y n).toMonoidHom.comp
        (AlgebraicGeometry.Scheme.Modules.schemeKPushforward f n) := by
  apply MonoidHom.ext
  intro x
  apply (Waldhausen.QuillenComparison.comparisonKEquiv
    (AlgebraicGeometry.Scheme.Modules.vectorBundleExactStructure Y) n).injective
  have hs := DFunLike.congr_fun (smallVectorBundleKMap_finiteFlatPushforward f n) x
  have hq := DFunLike.congr_fun
    (Waldhausen.QuillenComparison.comparisonKEquiv_exactFunctor_naturality
      (AlgebraicGeometry.Scheme.Modules.vectorBundlePushforwardExact f) n) (vectorBundleQSEquiv X n
        x)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hs hq ⊢
  simp only [vectorBundleQSEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply] at hq
  simpa only [vectorBundleQSEquiv, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
    ← AlgebraicGeometry.Scheme.Modules.smallVectorBundleKEquiv_coe, MonoidHom.coe_coe]
      using hq.trans hs.symm

/-- The original public vector-bundle-to-strict comparison is natural for
finite flat scheme morphisms, including in degree zero. -/
theorem vectorBundleToStrictKMap_finiteFlatPushforward {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [AlgebraicGeometry.IsFinite f] [Flat f] (n : ℕ) :
    (strictKFiniteFlatPushforward f n).comp (vectorBundleToStrictKMap X n) =
      (vectorBundleToStrictKMap Y n).comp (AlgebraicGeometry.Scheme.Modules.schemeKPushforward f n)
        := by
  unfold vectorBundleToStrictKMap
  rw [← MonoidHom.comp_assoc, vectorBundleSComparison_finiteFlatPushforward,
    MonoidHom.comp_assoc, vectorBundleQSEquiv_finiteFlatPushforward, MonoidHom.comp_assoc]

end Quillen.PerfectComplexes
