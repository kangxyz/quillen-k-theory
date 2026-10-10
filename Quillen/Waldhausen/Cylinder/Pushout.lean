/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.CategoryTheory.Limits.BiproductPushout
public import Quillen.Waldhausen.SplitComplexes.FactorizationFunctor
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-! # Actual pushout preservation of the complex cylinder functor

The identity cone is termwise the sum of the two neighboring evaluations.
This gives preservation of every displayed pushout, and then the original
middle functor preserves every componentwise pushout square of arrows.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex
universe u v
namespace Quillen.Waldhausen.SplitFactorization
variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Genuine pointwise pushouts detect a pushout of actual complexes. -/
theorem isPushout_of_degreewise
    {K L M N : CochainComplex A ℤ} {f : K ⟶ L} {g : K ⟶ M} {i : L ⟶ N} {j : M ⟶ N}
    (h : ∀ n, IsPushout (f.f n) (g.f n) (i.f n) (j.f n)) : IsPushout f g i j := by
  have w : f ≫ i = g ≫ j := by ext n; exact (h n).w
  apply IsPushout.of_isColimit (c := PushoutCocone.mk i j w)
  apply HomologicalComplex.isColimitOfEval
  intro n
  exact (isColimitMapCoconePushoutCoconeEquiv (eval A (ComplexShape.up ℤ) n) w).symm
    (h n).isColimit

/-- The actual identity-cone term is the genuine neighboring-term biproduct. -/
def identityConeTermIso (K : CochainComplex A ℤ) (n : ℤ) :
    (identityConeFunctor.obj K).X n ≅ K.X (n + 1) ⊞ K.X n where
  hom := biprod.lift ((mappingCone.fst (𝟙 K)).1.v n (n + 1) rfl)
    ((mappingCone.snd (𝟙 K)).v n n (add_zero n))
  inv := biprod.desc ((mappingCone.inl (𝟙 K)).v (n + 1) n (by omega))
    ((mappingCone.inr (𝟙 K)).f n)
  hom_inv_id := by
    dsimp only [identityConeFunctor]
    simp [mappingCone.ext_from_iff _ (n + 1) n rfl]
  inv_hom_id := by ext <;> simp

/-- The original cone map is the termwise actual biproduct map under this iso. -/
theorem identityConeTermIso_naturality {K L : CochainComplex A ℤ} (f : K ⟶ L) (n : ℤ) :
    (identityConeTermIso K n).hom ≫ biprod.map (f.f (n + 1)) (f.f n) =
      (identityConeFunctor.map f).f n ≫ (identityConeTermIso L n).hom := by
  apply biprod.hom_ext <;>
    simp [identityConeTermIso, identityConeFunctor, mappingCone.map,
      mappingCone.ext_from_iff _ (n + 1) n rfl]

/-- The actual identity-cone functor preserves every displayed pushout. -/
theorem identityConeFunctor_map_isPushout
    {K L M N : CochainComplex A ℤ} {f : K ⟶ L} {g : K ⟶ M} {i : L ⟶ N} {j : M ⟶ N}
    (h : IsPushout f g i j) :
    IsPushout (identityConeFunctor.map f) (identityConeFunctor.map g)
      (identityConeFunctor.map i) (identityConeFunctor.map j) := by
  apply isPushout_of_degreewise
  intro n
  have H := isPushout_biprod_map (h.map (eval A (ComplexShape.up ℤ) (n + 1)))
    (h.map (eval A (ComplexShape.up ℤ) n))
  apply H.of_iso (identityConeTermIso K n).symm (identityConeTermIso L n).symm
    (identityConeTermIso M n).symm (identityConeTermIso N n).symm
  all_goals simp only [Iso.symm_hom]; apply (cancel_epi (identityConeTermIso _ n).hom).1
  all_goals simp only [Iso.hom_inv_id_assoc]
  all_goals simp only [eval_map]
  all_goals rw [← Category.assoc, identityConeTermIso_naturality]
  all_goals simp

/-- The original cylinder middle functor preserves actual componentwise
pushouts of arrow squares, with no cofibration or weak-equivalence assumption. -/
theorem middleFunctor_map_isPushout
    {K L M N : Arrow (CochainComplex A ℤ)} {f : K ⟶ L} {g : K ⟶ M}
    {i : L ⟶ N} {j : M ⟶ N}
    (hL : IsPushout f.left g.left i.left j.left)
    (hR : IsPushout f.right g.right i.right j.right) :
    IsPushout (middleFunctor.map f) (middleFunctor.map g)
      (middleFunctor.map i) (middleFunctor.map j) :=
  isPushout_biprod_map (identityConeFunctor_map_isPushout hL) hR

end Quillen.Waldhausen.SplitFactorization
