/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Abelian.CommSq

/-! # Abelian bicartesian squares and actual cospan descent

Pushouts along a monomorphism are pullbacks, and pullbacks along an
epimorphism are pushouts. Their original square gives the displayed
cospan descent map with both literal leg equations.
-/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits
namespace Quillen
attribute [local instance] Abelian.hasFiniteBiproducts
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- An abelian pushout with a monic left leg is also an actual pullback. -/
theorem isPullback_of_isPushout_mono {A B D E : C}
    {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ E} {j : D ⟶ E}
    (sq : IsPushout f g i j) [Mono g] : IsPullback f g i j := by
  have : Mono sq.shortComplex.f := by
    change Mono (biprod.lift f (-g))
    exact mono_of_mono_fac (biprod.lift_snd f (-g))
  let hk := sq.exact_shortComplex.fIsKernel
  apply IsPullback.mk' sq.w
  · intro T a b _ h
    exact (cancel_mono g).1 h
  · intro T a b h
    let fork : KernelFork sq.shortComplex.g :=
      KernelFork.ofι (biprod.lift a (-b)) (by simp [CommSq.shortComplex, h])
    let l := hk.lift fork
    have hl : l ≫ biprod.lift f (-g) = biprod.lift a (-b) := hk.fac fork .zero
    refine ⟨l, ?_, ?_⟩
    · have hh := congrArg (fun k => k ≫ biprod.fst) hl
      simpa [Category.assoc] using hh
    · have hh := congrArg (fun k => k ≫ biprod.snd) hl
      simpa [Category.assoc] using hh

/-- An abelian pullback along an epimorphism is also a pushout. -/
theorem isPushout_of_isPullback_epi {A B D E : C}
    {f : A ⟶ B} {g : A ⟶ D} {i : B ⟶ E} {j : D ⟶ E}
    (sq : IsPullback f g i j) [Epi j] : IsPushout f g i j := by
  exact (isPullback_of_isPushout_mono sq.flip.op).unop.flip

namespace Q

/-- A map out of the codomain of a mono-epi cospan descends uniquely from
compatible maps on its legs. -/
def cospanDesc {X Y U V : C} (i : X ⟶ U) (p : Y ⟶ U) [Epi p]
    (a : X ⟶ V) (b : Y ⟶ V)
    (w : pullback.fst i p ≫ a = pullback.snd i p ≫ b) : U ⟶ V :=
  (isPushout_of_isPullback_epi (IsPullback.of_hasPullback i p)).desc a b w

@[reassoc (attr := simp)]
theorem cospanDesc_left {X Y U V : C} (i : X ⟶ U) (p : Y ⟶ U) [Epi p]
    (a : X ⟶ V) (b : Y ⟶ V)
    (w : pullback.fst i p ≫ a = pullback.snd i p ≫ b) :
    i ≫ cospanDesc i p a b w = a := by simp [cospanDesc]

@[reassoc (attr := simp)]
theorem cospanDesc_right {X Y U V : C} (i : X ⟶ U) (p : Y ⟶ U) [Epi p]
    (a : X ⟶ V) (b : Y ⟶ V)
    (w : pullback.fst i p ≫ a = pullback.snd i p ≫ b) :
    p ≫ cospanDesc i p a b w = b := by simp [cospanDesc]

end Q
end Quillen
