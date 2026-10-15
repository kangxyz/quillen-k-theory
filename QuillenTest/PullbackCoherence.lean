/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Quillen.AlgebraicGeometry.PerfectComplexes.PullbackCoherence

/-! Actual terms of the two geometric triple-pullback routes, for arbitrary scheme maps. -/
@[expose] public section

open Quillen.PerfectComplexes


noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
namespace QuillenTest.PullbackCoherence

open Quillen

variable {X Y Z T : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

lemma original_five_factor_terms (K : Complex T) (n : ℤ) :
    (((pullbackComplexCompIso f (g ≫ h)).hom ≫
      Functor.whiskerRight (pullbackComplexCompIso g h).hom
        (AlgebraicGeometry.Scheme.Modules.Complex.pullback f) ≫
      (Functor.associator (AlgebraicGeometry.Scheme.Modules.Complex.pullback h)
        (AlgebraicGeometry.Scheme.Modules.Complex.pullback g)
        (AlgebraicGeometry.Scheme.Modules.Complex.pullback f)).hom ≫
      Functor.whiskerLeft (AlgebraicGeometry.Scheme.Modules.Complex.pullback h)
        (pullbackComplexCompIso f g).inv ≫
      (pullbackComplexCompIso (f ≫ g) h).inv).app K).f n =
    (((eqToHom (by simp) : AlgebraicGeometry.Scheme.Modules.Complex.pullback (f ≫ g ≫ h) ⟶
      AlgebraicGeometry.Scheme.Modules.Complex.pullback ((f ≫ g) ≫ h))).app K).f n :=
  congrArg (fun η ↦ (η.app K).f n) (pullbackComplexCompIso_associativity f g h)

lemma original_two_route_terms (K : Complex T) (n : ℤ) :
    (((pullbackComplexCompIso f (g ≫ h)).hom ≫
      Functor.whiskerRight (pullbackComplexCompIso g h).hom
        (AlgebraicGeometry.Scheme.Modules.Complex.pullback f) ≫
      (Functor.associator (AlgebraicGeometry.Scheme.Modules.Complex.pullback h)
        (AlgebraicGeometry.Scheme.Modules.Complex.pullback g)
        (AlgebraicGeometry.Scheme.Modules.Complex.pullback f)).hom).app K).f n =
    (((eqToHom (by simp) : AlgebraicGeometry.Scheme.Modules.Complex.pullback (f ≫ g ≫ h) ⟶
      AlgebraicGeometry.Scheme.Modules.Complex.pullback ((f ≫ g) ≫ h)) ≫ (pullbackComplexCompIso (f
        ≫ g) h).hom ≫
      Functor.whiskerLeft (AlgebraicGeometry.Scheme.Modules.Complex.pullback h)
        (pullbackComplexCompIso f g).hom).app K).f n :=
  congrArg (fun η ↦ (η.app K).f n) (pullbackComplexCompIso_two_routes f g h)

end QuillenTest.PullbackCoherence
