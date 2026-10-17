/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Pullback


public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.Algebra.Homology.CochainComplex.Cycles
public import Aglib.Algebra.Homology.MappingCone.QuasiIso
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Pullback
public import Quillen.Aglib.AlgebraicGeometry.Modules.LocallyFree.KernelClosure
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.Closure
public import Aglib.Algebra.Homology.MappingCone.NullHomotopy
public import Aglib.AlgebraicGeometry.Modules.PerfectComplexes.LocalQuasiIsoLifting
public import Quillen.AlgebraicGeometry.PerfectComplexes.Restriction
public import Quillen.Waldhausen.Functoriality.KMap
public import Aglib.AlgebraicGeometry.Modules.Complex.Pullback

/-!
# Actual arbitrary pullback of strict-perfect complexes

Termwise geometric pullback preserves bounded finite-locally-free complexes,
their actual short exact sequences, and their quasi-isomorphisms. The K-map is
induced directly by this geometric functor, satisfies identity and composition,
and agrees with open restriction, including inverse-image-open squares.

This concerns globally strict-perfect complexes. It does not assert that
underived pullback preserves arbitrary locally perfect complexes.
-/
@[expose] public section

open AlgebraicGeometry.Scheme.Modules.Complex
open CategoryTheory.ExactCategory

open Quillen




noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Pretriangulated CochainComplex
universe u
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes

/-- Genuine arbitrary pullback is Waldhausen-exact on strict-perfect complexes. -/
theorem strictPullback_waldhausenExact {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Waldhausen.IsExact (strictWaldhausen Y).cof (strictWaldhausen Y).weq
      (strictWaldhausen X).cof (strictWaldhausen X).weq (strictPullback f) where
  zero h := (strictPullback f).map_isZero h
  cofibration s hs := (strictExactPullback f).map_inflation s hs
  weak {K L} s hs := by
    let : QuasiIso s.hom := hs
    exact quasiIso_pullback_of_strictPerfect f K.property L.property s.hom
  pushout hi h := by
    apply IsPushout.of_map_of_faithful (strictPerfect X).ι
    exact (Waldhausen.fullSubcategory_map_pushout (abelianExactStructure
      (CochainComplex Y.Modules ℤ))
      (strictPerfect Y) hi h).map (AlgebraicGeometry.Scheme.Modules.Complex.pullback f)

/-- The K-map is induced by the actual termwise strict-perfect pullback. -/
def strictKPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    StrictK Y n →* StrictK X n := Waldhausen.KMap (strictPullback_waldhausenExact f) n

@[simp high]
theorem strictKPullback_id (X : Scheme.{u}) (n : ℕ) :
    strictKPullback (𝟙 X) n = MonoidHom.id (StrictK X n) :=
  (Waldhausen.KMap_eq_of_iso (strictPullback_waldhausenExact (𝟙 X))
    (Waldhausen.IsExact.id (strictWaldhausen X).cof (strictWaldhausen X).weq)
    (strictPullbackIdIso X) n).trans (Waldhausen.KMap_id _ n)

@[simp high]
theorem strictKPullback_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    strictKPullback (f ≫ g) n = (strictKPullback f n).comp (strictKPullback g n) :=
  (Waldhausen.KMap_eq_of_iso (strictPullback_waldhausenExact (f ≫ g))
    ((strictPullback_waldhausenExact g).comp (strictPullback_waldhausenExact f))
    (strictPullbackCompIso f g) n).trans
    (Quillen.Waldhausen.KMap_comp_KMap
      (strictPullback_waldhausenExact g) (strictPullback_waldhausenExact f) n).symm

/-- The original geometric open-restriction K-map is retained. -/
theorem strictKPullback_eq_restrict {X Y : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (n : ℕ) :
    strictKPullback j n = strictKRestrict j n :=
  Waldhausen.KMap_eq_of_iso (strictPullback_waldhausenExact j)
    (strictRestrict_waldhausenExact j) (strictRestrictIsoPullback j).symm n

/-- The genuine pullback/restriction square commutes on the original K-maps. -/
theorem strictKPullback_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens) (n : ℕ) :
    (strictKRestrict (f ⁻¹ᵁ U).ι n).comp (strictKPullback f n) =
      (strictKPullback (f ∣_ U) n).comp (strictKRestrict U.ι n) := by
  unfold strictKPullback strictKRestrict
  rw [Quillen.Waldhausen.KMap_comp_KMap, Quillen.Waldhausen.KMap_comp_KMap]
  exact Waldhausen.KMap_eq_of_iso _ _ (strictPullbackRestrictIso f U) n

end Quillen.PerfectComplexes
