/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlat.Pullback


public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Basic
public import Quillen.Aglib.AlgebraicGeometry.Modules.PerfectComplexes.BoundedFlatPullback
public import Aglib.AlgebraicGeometry.Modules.Complex.Flat.BoundedPullback

/-!
# Genuine arbitrary pullback on bounded-flat locally-perfect complexes

The original geometric termwise pullback preserves the proved object
property. Actual flat-quotient short exactness and bounded-flat quasi-isomorphism
preservation give a genuine Waldhausen-exact functor for every scheme morphism.
No ambient sheaf exactness, flat-map premise or derived-to-K shortcut is used.
-/
@[expose] public section



open CategoryTheory.ExactCategory


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
open AlgebraicGeometry.Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes

variable {X : Scheme.{u}}

/-- The original geometric functor is genuinely Waldhausen-exact, not merely triangulated. -/
theorem boundedFlatPerfectPullback_exact {Y : Scheme.{u}} (f : X ⟶ Y) :
    Waldhausen.IsExact (boundedFlatPerfectWaldhausen Y).cof (boundedFlatPerfectWaldhausen Y).weq
      (boundedFlatPerfectWaldhausen X).cof (boundedFlatPerfectWaldhausen X).weq
      (boundedFlatPerfectPullback f) where
  zero h := (boundedFlatPerfectPullback f).map_isZero h
  cofibration p hp := (boundedFlatPerfectExactPullback f).map_inflation p hp
  weak {K L} p hp := by
    let : QuasiIso p.hom := hp
    obtain ⟨b, hb⟩ := K.property.2.1
    obtain ⟨c, hc⟩ := L.property.2.1
    exact quasiIso_pullback_of_boundedAbove_stalkwiseFlat f K.property.2.2 L.property.2.2 b c
      (fun n hn => K.obj.isZero_of_isStrictlyLE b n hn)
      (fun n hn => L.obj.isZero_of_isStrictlyLE c n hn) p.hom
  pushout hp hs := by
    apply IsPushout.of_map_of_faithful (boundedFlatPerfect X).ι
    exact (Waldhausen.fullSubcategory_map_pushout _ (boundedFlatPerfect Y) hp hs).map
      (AlgebraicGeometry.Scheme.Modules.Complex.pullback f)

end Quillen.PerfectComplexes
