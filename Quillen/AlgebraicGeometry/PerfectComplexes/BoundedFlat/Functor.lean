/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.Pullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.FlatPullback
public import Quillen.AlgebraicGeometry.PerfectComplexes.PullbackFunctor

/-!
# The actual bounded-flat K-functor and comparison maps

Actual termwise pullback induces the K-maps, with identity and composition
proved using the original geometric natural isomorphisms. Strict-to-flat and
flat-to-original-Perfect comparisons retain their literal inclusions. The
first is natural under all scheme maps; the second is compared with existing
flat Perf pullback. No comparison equivalence is assumed.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.CochainComplex Quillen.SchemeSheaf
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.PerfectComplexes

/-- The degree-`n` Waldhausen K-group of bounded-above, stalkwise-flat locally perfect complexes on
`X`. -/
abbrev BoundedFlatPerfectK (X : Scheme.{u}) (n : ℕ) := (boundedFlatPerfectWaldhausen X).K n

/-- The contravariant degree-`n` K-map from `Y` to `X` induced by termwise pullback of bounded-flat
perfect complexes along `f : X ⟶ Y`. -/
def boundedFlatPerfectKPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    BoundedFlatPerfectK Y n →* BoundedFlatPerfectK X n :=
  Waldhausen.KMap (boundedFlatPerfectPullback_exact f) n

/-- The natural isomorphism identifying pullback along the identity of `X` with the identity on
bounded-flat perfect complexes. -/
def boundedFlatPerfectPullbackIdIso (X : Scheme.{u}) :
    boundedFlatPerfectPullback (𝟙 X) ≅ 𝟭 (BoundedFlatPerfect X) :=
  Functor.fullyFaithfulCancelRight (boundedFlatPerfect X).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfect X).ι (pullbackComplexIdIso X))

/-- The natural isomorphism identifying pullback along `f ≫ g` with pullback first along `g` and
then along `f` on bounded-flat perfect complexes. -/
def boundedFlatPerfectPullbackCompIso {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    boundedFlatPerfectPullback (f ≫ g) ≅
      boundedFlatPerfectPullback g ⋙ boundedFlatPerfectPullback f :=
  Functor.fullyFaithfulCancelRight (boundedFlatPerfect X).ι
    (Functor.isoWhiskerLeft (boundedFlatPerfect Z).ι (pullbackComplexCompIso f g))

@[simp] theorem boundedFlatPerfectKPullback_id (X : Scheme.{u}) (n : ℕ) :
    boundedFlatPerfectKPullback (𝟙 X) n = MonoidHom.id (BoundedFlatPerfectK X n) :=
  (Waldhausen.KMap_eq_of_iso (boundedFlatPerfectPullback_exact (𝟙 X))
    (Waldhausen.IsExact.id (boundedFlatPerfectWaldhausen X).cof (boundedFlatPerfectWaldhausen
      X).weq)
    (boundedFlatPerfectPullbackIdIso X) n).trans (Waldhausen.KMap_id _ n)

@[simp] theorem boundedFlatPerfectKPullback_comp {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    boundedFlatPerfectKPullback (f ≫ g) n =
      (boundedFlatPerfectKPullback f n).comp (boundedFlatPerfectKPullback g n) :=
  (Waldhausen.KMap_eq_of_iso (boundedFlatPerfectPullback_exact (f ≫ g))
    ((boundedFlatPerfectPullback_exact g).comp (boundedFlatPerfectPullback_exact f))
    (boundedFlatPerfectPullbackCompIso f g) n).trans ((Waldhausen.KMap_comp_KMap _ _ n).symm)

/-- The contravariant group-valued functor on schemes given by degree-`n` K-theory of bounded-flat
perfect complexes and geometric pullback. -/
def BoundedFlatPerfectKFunctor (n : ℕ) : Scheme.{u}ᵒᵖ ⥤ GrpCat.{u + 1} where
  obj X := GrpCat.of (BoundedFlatPerfectK X.unop n)
  map f := GrpCat.ofHom (boundedFlatPerfectKPullback f.unop n)
  map_id X := by apply GrpCat.hom_ext; exact boundedFlatPerfectKPullback_id X.unop n
  map_comp f g := by apply GrpCat.hom_ext; exact boundedFlatPerfectKPullback_comp g.unop f.unop n

theorem strictPerfect_boundedFlatPerfect {X : Scheme.{u}} {K : Complex X}
    (hK : strictPerfect X K) : boundedFlatPerfect X K :=
  ⟨locallyPerfect_of_strictPerfect hK, strictPerfect_boundedAbove_stalkwiseFlat hK⟩

/-- The degree-`n` K-map induced by the inclusion of strictly perfect complexes into bounded-flat
perfect complexes on `X`. -/
def strictToBoundedFlatPerfectKMap (X : Scheme.{u}) (n : ℕ) :
    StrictK X n →* BoundedFlatPerfectK X n :=
  Waldhausen.subcategoryKMap (strictPerfect X) (boundedFlatPerfect X)
    (fun _ h => strictPerfect_boundedFlatPerfect h) n

/-- The degree-`n` K-map induced by the inclusion of bounded-flat perfect complexes into all
locally perfect complexes on `X`. -/
def boundedFlatPerfectToPerfectKMap (X : Scheme.{u}) (n : ℕ) :
    BoundedFlatPerfectK X n →* PerfectK X n :=
  Waldhausen.KMap (boundedFlatPerfectInclusion_exact X) n

theorem boundedFlatPerfectToPerfect_comp_strict (X : Scheme.{u}) (n : ℕ) :
    (boundedFlatPerfectToPerfectKMap X n).comp (strictToBoundedFlatPerfectKMap X n) =
      strictToPerfectKMap X n := by
  unfold boundedFlatPerfectToPerfectKMap strictToBoundedFlatPerfectKMap strictToPerfectKMap
    Waldhausen.subcategoryKMap
  rw [Waldhausen.KMap_comp_KMap]

theorem strictToBoundedFlatPerfectKMap_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (boundedFlatPerfectKPullback f n).comp (strictToBoundedFlatPerfectKMap Y n) =
      (strictToBoundedFlatPerfectKMap X n).comp (strictKPullback f n) := by
  unfold boundedFlatPerfectKPullback strictToBoundedFlatPerfectKMap strictKPullback
    Waldhausen.subcategoryKMap
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]

theorem boundedFlatPerfectToPerfectKMap_flatPullback {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] (n : ℕ) :
    (perfectKFlatPullback f n).comp (boundedFlatPerfectToPerfectKMap Y n) =
      (boundedFlatPerfectToPerfectKMap X n).comp (boundedFlatPerfectKPullback f n) := by
  unfold perfectKFlatPullback boundedFlatPerfectToPerfectKMap boundedFlatPerfectKPullback
  rw [Waldhausen.KMap_comp_KMap, Waldhausen.KMap_comp_KMap]

end Quillen.PerfectComplexes
