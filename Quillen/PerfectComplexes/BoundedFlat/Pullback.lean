/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.BoundedFlat.Basic
import Quillen.PerfectComplexes.BoundedFlatPullback

/-!
# Genuine arbitrary pullback on bounded-flat locally-perfect complexes

The original geometric termwise pullback preserves the proved object
property. Actual flat-quotient short exactness and bounded-flat quasi-isomorphism
preservation give a genuine Waldhausen-exact functor for every scheme morphism.
No ambient sheaf exactness, flat-map premise or derived-to-K shortcut is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
open Quillen.SchemeSheaf Quillen.CochainComplex
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes

variable {X : Scheme.{u}}

/-- Arbitrary geometric pullback preserves the actual bounded-flat perfect property. -/
theorem boundedFlatPerfect_pullback {Y : Scheme.{u}} (f : X ⟶ Y)
    {K : Complex Y} (hK : boundedFlatPerfect Y K) :
    boundedFlatPerfect X ((pullbackComplex f).obj K) := by
  obtain ⟨hp, ⟨b, hb⟩, hf⟩ := hK
  refine ⟨locallyPerfect_pullback_of_boundedAbove_stalkwiseFlat f hp ⟨b, hb⟩ hf,
    ⟨b, (CochainComplex.isStrictlyLE_iff _ _).mpr ?_⟩,
    fun n => stalkwiseFlat_pullback f (hf n)⟩
  intro n hn
  exact (Scheme.Modules.pullback f).map_isZero (K.isZero_of_isStrictlyLE b n hn)

/-- The functor is termwise geometric pullback on original complexes and original chain maps. -/
def boundedFlatPerfectPullback {Y : Scheme.{u}} (f : X ⟶ Y) :
    BoundedFlatPerfect Y ⥤ BoundedFlatPerfect X :=
  (boundedFlatPerfect X).lift ((boundedFlatPerfect Y).ι ⋙ pullbackComplex f)
    (fun K => boundedFlatPerfect_pullback f K.property)

instance boundedFlatPerfectPullback_additive {Y : Scheme.{u}} (f : X ⟶ Y) :
    (boundedFlatPerfectPullback f).Additive := by
  unfold boundedFlatPerfectPullback
  infer_instance

/-- Actual short exact sequences have flat quotient in each degree, so their pullbacks remain exact. -/
def boundedFlatPerfectExactPullback {Y : Scheme.{u}} (f : X ⟶ Y) :
    Quillen.ExactFunctor
      (ExactSubcategory.exactStructure (abelianExactStructure (Complex Y)) (boundedFlatPerfect Y))
      (ExactSubcategory.exactStructure (abelianExactStructure (Complex X)) (boundedFlatPerfect X)) where
  toFunctor := boundedFlatPerfectPullback f
  map_conflation S hS := by
    apply (HomologicalComplex.shortExact_iff_degreewise_shortExact _).mpr
    intro n
    exact shortExact_pullback_of_stalkwiseFlat_quotient f
      ((HomologicalComplex.shortExact_iff_degreewise_shortExact _).mp hS n)
      (S.X₃.property.2.2 n)

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
      (pullbackComplex f)

end Quillen.PerfectComplexes
