/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.PerfectComplexes.OpenFunctor

noncomputable section
open CategoryTheory AlgebraicGeometry Quillen.PerfectComplexes
universe u

example {X Y : Quillen.Scheme.OpenImmersionSchemes.{u}ᵒᵖ} (f : X ⟶ Y) :
    ((PerfectKOpenFunctor 0).map f).hom = perfectKRestrict f.unop.hom 0 := rfl

example {X Y : Quillen.Scheme.OpenImmersionSchemes.{u}ᵒᵖ} (f : X ⟶ Y) :
    ((StrictKOpenFunctor 0).map f).hom = strictKRestrict f.unop.hom 0 := rfl

example {X Y Z : Quillen.Scheme.OpenImmersionSchemes.{u}ᵒᵖ}
    (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) (x : PerfectK X.unop.obj n) :
    ((PerfectKOpenFunctor n).map (f ≫ g)).hom x =
      ((PerfectKOpenFunctor n).map g).hom (((PerfectKOpenFunctor n).map f).hom x) := by
  rw [Functor.map_comp]
  rfl

example {X Y : Quillen.Scheme.OpenImmersionSchemes.{u}ᵒᵖ} (f : X ⟶ Y) (n : ℕ) :
    (StrictKOpenFunctor n).map f ≫ (strictToPerfectOpenNatTrans n).app Y =
      (strictToPerfectOpenNatTrans n).app X ≫ (PerfectKOpenFunctor n).map f :=
  (strictToPerfectOpenNatTrans n).naturality f

example (X : Quillen.Scheme.OpenImmersionSchemes.{u}ᵒᵖ) (n : ℕ)
    (x : Quillen.Scheme.K X.unop.obj n) :
    ((vectorBundleToStrictOpenNatIso n).inv.app X).hom
      (((vectorBundleToStrictOpenNatIso n).hom.app X).hom x) = x :=
  (vectorBundleToStrictKEquiv X.unop.obj n).symm_apply_apply x

example (X : Quillen.Scheme.OpenImmersionSchemes.{u}ᵒᵖ) (n : ℕ)
    (x : StrictK X.unop.obj n) :
    ((vectorBundleToStrictOpenNatIso n).hom.app X).hom
      (((vectorBundleToStrictOpenNatIso n).inv.app X).hom x) = x :=
  (vectorBundleToStrictKEquiv X.unop.obj n).apply_symm_apply x

example (n : ℕ) :
    (vectorBundleToStrictOpenNatIso.{u} n).hom ≫ strictToPerfectOpenNatTrans n =
      vectorBundleToPerfectOpenNatTrans n := vectorBundleToStrictOpenNatIso_comp n

example {X Y : Quillen.Scheme.OpenImmersionSchemes.{u}ᵒᵖ} (f : X ⟶ Y) :
    (StrictKOpenFunctor 0).map f ≫ (vectorBundleToStrictOpenNatIso 0).inv.app Y =
      (vectorBundleToStrictOpenNatIso 0).inv.app X ≫ (Quillen.Scheme.KOpenFunctor 0).map f :=
  (vectorBundleToStrictOpenNatIso 0).inv.naturality f
