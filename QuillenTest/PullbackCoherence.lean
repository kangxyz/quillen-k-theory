/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.PullbackCoherence

/-! Actual terms of the two geometric triple-pullback routes, for arbitrary scheme maps. -/
@[expose] public section

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
universe u
namespace QuillenTest.PullbackCoherence

open Quillen

variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

lemma original_five_factor_terms (K : Complex T) (n : ℤ) :
    (((pullbackComplexCompIso f (g ≫ h)).hom ≫
      Functor.whiskerRight (pullbackComplexCompIso g h).hom (pullbackComplex f) ≫
      (Functor.associator (pullbackComplex h) (pullbackComplex g) (pullbackComplex f)).hom ≫
      Functor.whiskerLeft (pullbackComplex h) (pullbackComplexCompIso f g).inv ≫
      (pullbackComplexCompIso (f ≫ g) h).inv).app K).f n =
    (((eqToHom (by simp) : pullbackComplex (f ≫ g ≫ h) ⟶
      pullbackComplex ((f ≫ g) ≫ h))).app K).f n :=
  congrArg (fun η ↦ (η.app K).f n) (pullbackComplexCompIso_associativity f g h)

lemma original_two_route_terms (K : Complex T) (n : ℤ) :
    (((pullbackComplexCompIso f (g ≫ h)).hom ≫
      Functor.whiskerRight (pullbackComplexCompIso g h).hom (pullbackComplex f) ≫
      (Functor.associator (pullbackComplex h) (pullbackComplex g)
        (pullbackComplex f)).hom).app K).f n =
    (((eqToHom (by simp) : pullbackComplex (f ≫ g ≫ h) ⟶
      pullbackComplex ((f ≫ g) ≫ h)) ≫ (pullbackComplexCompIso (f ≫ g) h).hom ≫
      Functor.whiskerLeft (pullbackComplex h) (pullbackComplexCompIso f g).hom).app K).f n :=
  congrArg (fun η ↦ (η.app K).f n) (pullbackComplexCompIso_two_routes f g h)

end QuillenTest.PullbackCoherence
