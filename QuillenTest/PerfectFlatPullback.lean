/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.FlatPullbackFunctor

/-!
# Consumers of actual flat pullback on locally-perfect K-theory

These exercise arbitrary ambient complexes and genuinely local perfectness,
then identity/composition/open squares and the original public comparisons.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes
universe u
namespace QuillenTest.PerfectFlatPullback

/-- Quasi-isomorphism preservation is ambient, with no perfectness or QC premise. -/
theorem arbitraryQuasiIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {K L : Complex Y} (s : K ⟶ L) [QuasiIso s] : QuasiIso ((pullbackComplex f).map s) :=
  inferInstance

/-- An actual derived local model pulls back using genuine flatness alone. -/
def actualDerivedIso {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    {K L : Complex Y} (e : (toDerived Y).obj K ≅ (toDerived Y).obj L) :
    (toDerived X).obj ((pullbackComplex f).obj K) ≅
      (toDerived X).obj ((pullbackComplex f).obj L) := flatPullbackDerivedIso f e

/-- The input is a genuinely locally-perfect complex, with no global strict model. -/
theorem localPerfectness {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f]
    (K : Perfect Y) : locallyPerfect X ((pullbackComplex f).obj K.obj) :=
  locallyPerfect_flatPullback f K.property

/-- The K-map is directly induced by the geometric Waldhausen-exact functor. -/
theorem actualKMap {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (n : ℕ) :
    perfectKFlatPullback f n = Quillen.Waldhausen.KMap (perfectFlatPullback_waldhausenExact f) n :=
      rfl

/-- Composition retains the original underlying perfect K-groups. -/
theorem composite {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f] [Flat g]
    (n : ℕ) (a : PerfectK Z n) :
    perfectKFlatPullback (f ≫ g) n a = perfectKFlatPullback f n (perfectKFlatPullback g n a) :=
  DFunLike.congr_fun (perfectKFlatPullback_comp f g n) a

/-- Flat identity acts as the identity, in every connective degree including zero. -/
theorem identity (X : Scheme.{u}) (n : ℕ) (a : PerfectK X n) :
    perfectKFlatPullback (𝟙 X) n a = a := DFunLike.congr_fun (perfectKFlatPullback_id X n) a

/-- The flat map recovers the already-established geometric open restriction. -/
theorem openRestriction {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (n : ℕ) : perfectKFlatPullback j n = perfectKRestrict j n :=
  perfectKFlatPullback_eq_restrict j n

/-- The inverse-image-open square commutes on the original K-maps. -/
theorem inverseImageOpen {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (U : Y.Opens) (n : ℕ) :
    (perfectKRestrict (f ⁻¹ᵁ U).ι n).comp (perfectKFlatPullback f n) =
      (perfectKFlatPullback (f ∣_ U) n).comp (perfectKRestrict U.ι n) :=
  perfectKFlatPullback_restrict f U n

/-- Naturality retains the original public vector-bundle comparison. -/
theorem originalPublicComparison {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (n : ℕ) :
    (perfectKFlatPullback f n).comp (vectorBundleToPerfectKMap Y n) =
      (vectorBundleToPerfectKMap X n).comp (AlgebraicGeometry.Scheme.pullbackK f n) :=
  vectorBundleToPerfectKMap_flatPullback f n

/-- The bundled functor's maps are the geometric maps, rather than transported comparison maps. -/
theorem bundledMap {X Y : AlgebraicGeometry.Scheme.FlatSchemes.{u}ᵒᵖ} (f : X ⟶ Y) (n : ℕ) :
    ((PerfectKFlatFunctor n).map f).hom = perfectKFlatPullback f.unop.hom n := rfl

/-- The natural transformation's components are the original public comparison. -/
theorem bundledComparison (X : AlgebraicGeometry.Scheme.FlatSchemes.{u}ᵒᵖ) (n : ℕ) :
    ((vectorBundleToPerfectFlatNatTrans n).app X).hom = vectorBundleToPerfectKMap X.unop.obj n :=
      rfl

end QuillenTest.PerfectFlatPullback
