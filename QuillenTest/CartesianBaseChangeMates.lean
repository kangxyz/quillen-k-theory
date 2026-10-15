/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.CartesianBaseChangePasting
public import Quillen.AlgebraicGeometry.Scheme.Sheaf.DerivedFlatBaseChangeOpen

/-! # Original cartesian mate pasting and open-specialization consumers -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace QuillenTest.CartesianBaseChangeMates

open Quillen
open AlgebraicGeometry.Scheme.Modules Scheme.Modules
/-- The original standard ambient categories. -/
local instance standard (X : Scheme.{u}) : HasDerivedCategory.{u+1} X.Modules :=
  HasDerivedCategory.standard _
variable {Z' Z W U V X : Scheme.{u}}
  (c : Z' ⟶ Z) (d : Z' ⟶ W) (g : Z ⟶ U)
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (hs : IsPullback c d g a) (h : IsPullback a b f j)
/-- Original chart-composition arrows agree under the literal geometric mates. -/
theorem original_pasted_mate (M : Z.Modules) :
    (Scheme.Modules.pullback j).map ((pushforwardComp g f).hom.app M) ≫
        (cartesianBaseChangeMap c (d ≫ b) (g ≫ f) j (hs.paste_vert h)).app M ≫
        (pushforwardComp d b).inv.app ((Scheme.Modules.pullback c).obj M) =
      (cartesianBaseChangeMap a b f j h).app ((pushforward g).obj M) ≫
        (pushforward b).map ((cartesianBaseChangeMap c d g a hs).app M) :=
  cartesianBaseChangeMap_paste c d g a b f j hs h M
/-- The original ordinary pullback mate has the exact restriction comparison. -/
theorem original_restriction_comparison [IsOpenImmersion a] [IsOpenImmersion j]
    (M : U.Modules) :
    (restrictFunctorIsoPullback j).hom.app ((pushforward f).obj M) ≫
        (cartesianBaseChangeMap a b f j h).app M =
      (cartesianOpenBaseChange a b f j h).hom.app M ≫
        (pushforward b).map ((restrictFunctorIsoPullback a).hom.app M) :=
  cartesianBaseChangeMap_restrict a b f j h M
/-- On arbitrary bounded-below objects the literal derived mate has an inverse. -/
theorem original_derived_inverse [IsOpenImmersion j] (K : DerivedCategory.Plus U.Modules) :
    letI := isIso_derivedFlatBaseChangeMap_of_open a b f j h
    (derivedFlatBaseChangeMap a b f j h).app K ≫
      inv ((derivedFlatBaseChangeMap a b f j h).app K) = 𝟙 _ := by
  have := isIso_derivedFlatBaseChangeMap_of_open a b f j h
  simp
/-- The inverse retains the original ordinary mate and both installed derived units. -/
theorem original_inverse_unit [IsOpenImmersion j] (K : CochainComplex.Plus U.Modules) :
    letI := isIso_derivedFlatBaseChangeMap_of_open a b f j h
    letI := flat_cartesian_baseChange a b f j h
    DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pullback a)
        (pushforward b)).app K ≫
      inv ((derivedFlatBaseChangeMap a b f j h).app (DerivedCategory.Plus.Q.obj K)) =
    (Functor.rightDerivedFunctorPlusCompUnit (pushforward f)
      (Scheme.Modules.pullback j)).app K := by
  have := isIso_derivedFlatBaseChangeMap_of_open a b f j h
  rw [← Category.assoc, ← derivedFlatBaseChangeMap_unit a b f j h K]
  simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
end QuillenTest.CartesianBaseChangeMates
