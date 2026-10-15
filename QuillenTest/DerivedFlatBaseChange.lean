/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineDerivedBaseChange

/-! # Consumers of the original derived flat base-change map -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace QuillenTest.DerivedFlatBaseChange

open Quillen
/-- Use the actual standard ambient derived categories. -/
local instance standard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
open AlgebraicGeometry.Scheme.Modules
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j) [Flat j]
include h in
/-- The actual pulled-back leg inherits flatness from the original square. -/
theorem original_flat_leg : Flat a := flat_cartesian_baseChange a b f j h
/-- The exact comparison retains the ordinary mate and the installed composite units. -/
theorem original_unit_square (K : CochainComplex.Plus U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward f)
        (Scheme.Modules.pullback j)).app K ≫
      (derivedFlatBaseChangeMap a b f j h).app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pullback a)
        (Scheme.Modules.pushforward b)).app K :=
  derivedFlatBaseChangeMap_unit a b f j h K
/-- Naturality applies to arbitrary arrows of the actual bounded-below derived category. -/
theorem original_naturality {K L : DerivedCategory.Plus U.Modules} (g : K ⟶ L) :
    letI := flat_cartesian_baseChange a b f j h
    (derivedPushforwardPlus f ⋙ derivedFlatPullbackPlus j).map g ≫
        (derivedFlatBaseChangeMap a b f j h).app L =
      (derivedFlatBaseChangeMap a b f j h).app K ≫
        (derivedFlatPullbackPlus a ⋙ derivedPushforwardPlus b).map g :=
  (derivedFlatBaseChangeMap a b f j h).naturality g
variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B]
  (hc : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (Spec.map (CommRingCat.ofHom (algebraMap S B)))
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  [Flat (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
/-- The inverse is an inverse of the literal derived mate on the actual affine QC single. -/
theorem original_inverse (M : (Spec (CommRingCat.of A)).Modules) [M.IsQuasicoherent] :
    letI := isIso_derivedFlatBaseChangeMap_single R S A B hc M
    (derivedFlatBaseChangeMap _ _ _ _ hc).app
        (DerivedCategory.Plus.Q.obj (singleZeroPlus (Spec (CommRingCat.of A)) M)) ≫
      inv ((derivedFlatBaseChangeMap _ _ _ _ hc).app
        (DerivedCategory.Plus.Q.obj (singleZeroPlus (Spec (CommRingCat.of A)) M))) = 𝟙 _ := by
  have := isIso_derivedFlatBaseChangeMap_single R S A B hc M
  simp
end QuillenTest.DerivedFlatBaseChange
