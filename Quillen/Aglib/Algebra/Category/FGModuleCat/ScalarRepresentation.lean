/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.FGModuleCat.Basic
public import Quillen.Aglib.CategoryTheory.ExactCategory.Filtration.CentralEndomorphism

/-!
# Scalar maps through a fully faithful finite-module representation

Scalar multiplication lifts through a fully faithful finite-module representation with
independent ring and category universes. Additivity identifies zero and nilpotent scalar actions.
-/
@[expose] public section

noncomputable section
universe u v w
open CategoryTheory CategoryTheory.Limits
open Quillen.PrincipalSupportDevissage

namespace AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Principal
namespace ScalarRepresentation

variable {C : Type w} [Category.{v} C] [Abelian C]
  {A : Type u} [CommRing A] (F : C ⥤ FGModuleCat.{u} A) [F.Full] [F.Faithful]

/-- Scalar multiplication lifted through a fully faithful representation,
with independent ring and category universes. -/
def scalar (f : A) : 𝟭 C ⟶ 𝟭 C where
  app X := F.preimage (FGModuleCat.ofHom (LinearMap.lsmul A (F.obj X) f))
  naturality {X Y} a := by
    apply F.map_injective
    simp only [Functor.id_map, Functor.map_comp, Functor.map_preimage]
    ext m
    exact ((F.map a).hom.hom.map_smul f m).symm

omit [Abelian C] in
@[simp] theorem map_scalar (f : A) (X : C) :
    F.map ((scalar F f).app X) = FGModuleCat.ofHom (LinearMap.lsmul A (F.obj X) f) :=
  F.map_preimage _

omit [Abelian C] in
theorem map_power_apply (f : A) (X : C) (n : ℕ) (m : F.obj X) :
    (F.map (power (scalar F f) X n)).hom.hom m = f ^ n • m := by
  induction n with
  | zero => simp [power]
  | succ n ih =>
    simp only [power_succ, Functor.map_comp, map_scalar]
    change (F.map (power (scalar F f) X n)).hom.hom (f • m) = f ^ (n + 1) • m
    rw [_root_.map_smul, ih, smul_smul, pow_succ']

variable [F.Additive]

theorem killed_iff (f : A) (X : C) :
    killed (scalar F f) X ↔ ∀ m : F.obj X, f • m = 0 := by
  change (scalar F f).app X = 0 ↔ _
  rw [← F.map_injective.eq_iff, map_scalar, F.map_zero]
  constructor
  · intro h m
    exact congrArg (fun a ↦ a.hom.hom m) h
  · intro h
    ext m
    exact h m

theorem power_eq_zero (f : A) (X : C) (n : ℕ)
    (h : ∀ m : F.obj X, f ^ n • m = 0) : power (scalar F f) X n = 0 := by
  apply F.map_injective
  rw [F.map_zero]
  ext m
  exact (map_power_apply F f X n m).trans (h m)

end ScalarRepresentation
end AlgebraicGeometry.Scheme.Modules.Coherent.Pushforward.ClosedImmersion.Principal
