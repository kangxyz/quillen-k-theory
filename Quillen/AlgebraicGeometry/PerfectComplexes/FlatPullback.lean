/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.FlatPullback


public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.CategoryTheory.ExactCategory.Functor
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.AlgebraicGeometry.Modules.Pullback.FlatMorphism
public import Quillen.AlgebraicGeometry.PerfectComplexes.PullbackNaturality
public import Quillen.AlgebraicGeometry.PerfectComplexes.RestrictionFunctoriality
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Local

public import Aglib.AlgebraicGeometry.Modules.DerivedCategory.Basic
public import Aglib.AlgebraicGeometry.Modules.Complex.Pullback
/-!
# Genuine flat pullback of locally perfect complexes

Actual flat geometric pullback is exact on all module sheaves. Hence its
termwise complex functor preserves every actual quasi-isomorphism, descends
to the existing derived localization, and preserves the original genuinely
local strict-model predicate. The resulting maps on the original Waldhausen
K-groups satisfy identity, composition, open restriction, and comparison
naturality. No global strict representative is required.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
open Quillen





open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
attribute [local instance] AlgebraicGeometry.Scheme.Modules.standardHasDerivedCategory
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.PerfectComplexes

/-- Actual flat pullback is exact for the original locally-perfect Waldhausen categories. -/
theorem perfectFlatPullback_waldhausenExact {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] :
    Waldhausen.IsExact (perfectWaldhausen Y).cof (perfectWaldhausen Y).weq
      (perfectWaldhausen X).cof (perfectWaldhausen X).weq (perfectFlatPullback f) where
  zero h := (perfectFlatPullback f).map_isZero h
  cofibration s hs := (perfectExactFlatPullback f).map_inflation s hs
  weak s hs := by
    let : QuasiIso s.hom := hs
    exact AlgebraicGeometry.Scheme.Modules.Complex.pullback_quasiIso f s.hom
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (locallyPerfect X).ι
    exact (Waldhausen.fullSubcategory_map_pushout (abelianExactStructure
      (CochainComplex Y.Modules ℤ))
      (locallyPerfect Y) hi h).map (AlgebraicGeometry.Scheme.Modules.Complex.pullback f)

/-- The original perfect K-groups carry the genuine flat geometric pullback K-map. -/
def perfectKFlatPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (n : ℕ) :
    PerfectK Y n →* PerfectK X n := Waldhausen.KMap (perfectFlatPullback_waldhausenExact f) n

@[simp high]
theorem perfectKFlatPullback_id (X : Scheme.{u}) (n : ℕ) :
    perfectKFlatPullback (𝟙 X) n = MonoidHom.id (PerfectK X n) :=
  (Waldhausen.KMap_eq_of_iso (perfectFlatPullback_waldhausenExact (𝟙 X))
    (Waldhausen.IsExact.id (perfectWaldhausen X).cof (perfectWaldhausen X).weq)
    (perfectFlatPullbackIdIso X) n).trans (Waldhausen.KMap_id _ n)

@[simp high]
theorem perfectKFlatPullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Flat f] [Flat g] (n : ℕ) :
    perfectKFlatPullback (f ≫ g) n = (perfectKFlatPullback f n).comp (perfectKFlatPullback g n) :=
  (Waldhausen.KMap_eq_of_iso (perfectFlatPullback_waldhausenExact (f ≫ g))
    ((perfectFlatPullback_waldhausenExact g).comp (perfectFlatPullback_waldhausenExact f))
    (perfectFlatPullbackCompIso f g) n).trans ((Waldhausen.KMap_comp_KMap _ _ n).symm)

/-- The original geometric open-restriction map is recovered without changing the model. -/
theorem perfectKFlatPullback_eq_restrict {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (n : ℕ) : perfectKFlatPullback j n = perfectKRestrict j n :=
  Waldhausen.KMap_eq_of_iso (perfectFlatPullback_waldhausenExact j)
    (perfectRestrict_waldhausenExact j) (perfectRestrictIsoFlatPullback j).symm n

/-- Actual flat pullback/restriction naturality on the existing perfect K-groups. -/
theorem perfectKFlatPullback_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (U : Y.Opens) (n : ℕ) :
    (perfectKRestrict (f ⁻¹ᵁ U).ι n).comp (perfectKFlatPullback f n) =
      (perfectKFlatPullback (f ∣_ U) n).comp (perfectKRestrict U.ι n) := by
  unfold perfectKFlatPullback perfectKRestrict
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]
  exact Waldhausen.KMap_eq_of_iso _ _ (perfectFlatPullbackRestrictIso f U) n

/-- The original strict-to-locally-perfect comparison commutes with actual flat pullback. -/
theorem strictToPerfectKMap_flatPullback {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (n : ℕ) :
    (perfectKFlatPullback f n).comp (strictToPerfectKMap Y n) =
      (strictToPerfectKMap X n).comp (strictKPullback f n) := by
  unfold perfectKFlatPullback strictToPerfectKMap strictKPullback Waldhausen.subcategoryKMap
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]

/-- The original public vector-bundle-to-perfect comparison is natural for flat morphisms. -/
theorem vectorBundleToPerfectKMap_flatPullback {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] (n : ℕ) :
    (perfectKFlatPullback f n).comp (vectorBundleToPerfectKMap Y n) =
      (vectorBundleToPerfectKMap X n).comp (AlgebraicGeometry.Scheme.pullbackK f n) := by
  rw [← strictToPerfect_comp_vectorBundleToStrictKMap,
    ← strictToPerfect_comp_vectorBundleToStrictKMap,
    ← MonoidHom.comp_assoc, strictToPerfectKMap_flatPullback,
    MonoidHom.comp_assoc, vectorBundleToStrictKMap_pullback, MonoidHom.comp_assoc]

end Quillen.PerfectComplexes
