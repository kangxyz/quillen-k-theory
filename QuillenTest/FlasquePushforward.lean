/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.Scheme.Sheaf.FlasqueDerivedPushforward

/-!
# Original flasque direct-image consumers

Inspect the original differential maps of an arbitrary injective resolution,
higher direct images of pushforward injectives, and the actual installed unit
and its inverse on singles and genuinely bounded complexes.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry HomologicalComplex
open AlgebraicGeometry.Scheme.Modules
namespace QuillenTest.FlasquePushforward


/-- The standard ambient derived category for the original direct-image functors. -/
local instance flasquePushforwardStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- The actual degree-one resolution differentials become an exact original short complex. -/
theorem original_resolution_exact {X Y : Scheme.{u}} (f : X ⟶ Y) (M : X.Modules)
    [TopCat.Presheaf.IsFlasque M.presheaf] (I : InjectiveResolution M) :
    (ShortComplex.mk ((Scheme.Modules.pushforward f).map (I.cocomplex.d 0 1))
      ((Scheme.Modules.pushforward f).map (I.cocomplex.d 1 2))
      (by rw [← Functor.map_comp, I.cocomplex.d_comp_d, Functor.map_zero])).Exact := by
  have h := pushforward_injectiveResolution_exact_succ_of_flasque f M I 0
  exact (HomologicalComplex.exactAt_iff' _ 0 1 2 (by simp) (by simp)).mp h

/-- Higher derived image of the original pushforward of an injective has only zero arrows. -/
theorem original_composite_acyclic {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : X.Modules) [Injective I] (n : ℕ) (N : Z.Modules)
    (h : (((Scheme.Modules.pushforward g).rightDerived (n + 1)).obj
      ((Scheme.Modules.pushforward f).obj I)) ⟶ N) : h = 0 :=
  (isZero_rightDerived_pushforward_succ_of_flasque g
    ((Scheme.Modules.pushforward f).obj I) n).eq_of_src h 0

/-- The original installed unit on a pushforward injective has an actual inverse. -/
theorem original_single_unit_inverse {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : X.Modules) [Injective I] :
    letI := isIso_derivedPushforwardPlusUnit_single_of_flasque g
      ((Scheme.Modules.pushforward f).obj I)
    (derivedPushforwardPlusUnit g).app
        (singleZeroPlus Y ((Scheme.Modules.pushforward f).obj I)) ≫
      inv ((derivedPushforwardPlusUnit g).app
        (singleZeroPlus Y ((Scheme.Modules.pushforward f).obj I))) = 𝟙 _ := by
  let := isIso_derivedPushforwardPlusUnit_single_of_flasque g
    ((Scheme.Modules.pushforward f).obj I)
  exact IsIso.hom_inv_id _

/-- Genuine lower and upper term bounds make the original complex unit invertible. -/
theorem original_bounded_unit_inverse {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex.Plus X.Modules) (a b : ℤ)
    (hl : ∀ i, i < a → IsZero (K.obj.X i))
    (hu : ∀ i, b < i → IsZero (K.obj.X i))
    (hK : ∀ i, TopCat.Presheaf.IsFlasque (K.obj.X i).presheaf) :
    letI := isIso_derivedPushforwardPlusUnit_of_flasque_term_bounds f K a b hl hu hK
    inv ((derivedPushforwardPlusUnit f).app K) ≫
      (derivedPushforwardPlusUnit f).app K = 𝟙 _ := by
  let := isIso_derivedPushforwardPlusUnit_of_flasque_term_bounds f K a b hl hu hK
  exact IsIso.inv_hom_id _

end QuillenTest.FlasquePushforward
