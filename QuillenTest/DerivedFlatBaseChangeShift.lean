/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatBaseChangeShift
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.AffineDerivedBaseChange

/-! # Original shifted derived base-change consumers -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace QuillenTest.DerivedFlatBaseChangeShift

open Quillen
open AlgebraicGeometry.Scheme.Modules
/-- The original standard ambient categories. -/
local instance standard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j) [Flat j]
/-- The literal derived mate commutes with the actual shift isomorphisms. -/
theorem original_shift_square (K : DerivedCategory.Plus U.Modules) (n : ℤ) :
    letI := flat_cartesian_baseChange a b f j h
    ((derivedPushforwardPlus f ⋙ derivedFlatPullbackPlus j).commShiftIso n).hom.app K ≫
        ((derivedFlatBaseChangeMap a b f j h).app K)⟦n⟧' =
      (derivedFlatBaseChangeMap a b f j h).app (K⟦n⟧) ≫
        ((derivedFlatPullbackPlus a ⋙ derivedPushforwardPlus b).commShiftIso n).hom.app K := by
  have := derivedFlatBaseChangeMap_commShift a b f j h
  exact NatTrans.shift_app_comm (derivedFlatBaseChangeMap a b f j h) n K
/-- The original factorization equation also holds on the literal shifted complex. -/
theorem original_shifted_unit (K : CochainComplex.Plus U.Modules) (n : ℤ) :
    letI := flat_cartesian_baseChange a b f j h
    (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward f)
        (Scheme.Modules.pullback j)).app (K⟦n⟧) ≫
      (derivedFlatBaseChangeMap a b f j h).app (DerivedCategory.Plus.Q.obj (K⟦n⟧)) =
    DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app (K⟦n⟧)) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pullback a)
        (Scheme.Modules.pushforward b)).app (K⟦n⟧) :=
  derivedFlatBaseChangeMap_unit a b f j h (K⟦n⟧)
variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B]
  (hc : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    (Spec.map (CommRingCat.ofHom (algebraMap S B)))
    (Spec.map (CommRingCat.ofHom (algebraMap R A)))
    (Spec.map (CommRingCat.ofHom (algebraMap R S))))
  [Flat (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
/-- Every actual shifted affine QC single is sent by an invertible original derived mate. -/
theorem original_shifted_single (M : (Spec (CommRingCat.of A)).Modules)
    [M.IsQuasicoherent] (n : ℤ) :
    IsIso ((derivedFlatBaseChangeMap _ _ _ _ hc).app
      ((DerivedCategory.Plus.Q.obj (singleZeroPlus (Spec (CommRingCat.of A)) M))⟦n⟧)) := by
  have := derivedFlatBaseChangeMap_commShift _ _ _ _ hc
  have := isIso_derivedFlatBaseChangeMap_single R S A B hc M
  rw [NatTrans.app_shift (derivedFlatBaseChangeMap _ _ _ _ hc)]
  infer_instance
end QuillenTest.DerivedFlatBaseChangeShift
