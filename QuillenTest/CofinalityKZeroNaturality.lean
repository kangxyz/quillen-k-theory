/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Waldhausen.Cofinality.ImageReflection

/-! # Cofinality and K-zero naturality consumers -/
@[expose] public section

open Quillen.Waldhausen



noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
namespace QuillenTest.GradedKZeroNaturality
open Quillen.Waldhausen.Cofinality

section Small
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {W : Structure C} {V : Structure D} [HasBinaryCoproducts C] [HasBinaryCoproducts D]
  {P : ObjectProperty C} {Q : ObjectProperty D}
  (h : DenseCofiberData W P) (k : DenseCofiberData V Q) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F) (hp : ∀ A, P A → Q (F.obj A))
  (Dd : Fibration.RowFactorization.JointData (.refl W))
  (De : Fibration.RowFactorization.JointData (.refl V))

/-- The original fine K-map respects the actual complement obstruction. -/
theorem actual_obstruction_square (x : W.K 0) :
    (h.classMap k hF hp).toMultiplicative (h.classKZeroMap Dd x) =
      k.classKZeroMap De (KMap hF 0 x) :=
  DFunLike.congr_fun (h.classKZeroMap_natural k hF hp Dd De) x

include k hp De in
/-- Equality after restriction in the original fine K-zero group implies
exact equality of the source complement obstructions when membership reflects. -/
theorem original_equality_reflects_obstruction (hback : ∀ A, Q (F.obj A) → P A)
    (x y : W.K 0) (hxy : KMap hF 0 x = KMap hF 0 y) :
    h.classKZeroMap Dd x = h.classKZeroMap Dd y := by
  apply h.classMap_injective k hF hp hback
  change (h.classMap k hF hp).toMultiplicative (h.classKZeroMap Dd x) =
    (h.classMap k hF hp).toMultiplicative (h.classKZeroMap Dd y)
  rw [actual_obstruction_square h k hF hp Dd De, actual_obstruction_square h k hF hp Dd De, hxy]

end Small
section General
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {V : Structure D} [HasBinaryCoproducts C] [HasBinaryCoproducts D]
  {P : ObjectProperty C} {Q : ObjectProperty D}
  (h : DenseCofiberData W P) (k : DenseCofiberData V Q) {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F) (hp : ∀ A, P A ↔ Q (F.obj A))
  (Dd : Fibration.RowFactorization.JointData (.refl W))
  (De : Fibration.RowFactorization.JointData (.refl V))
  (hsd : Fibration.RowFactorization.SecondEndpointSection (.refl W) Dd)
  (hse : Fibration.RowFactorization.SecondEndpointSection (.refl V) De)

include hp Dd De hsd hse in
/-- An actual image lift after the exact functor yields an actual source-image
class, with independent object and hom universes. -/
theorem original_image_lift (x : W.K 0) (y : k.waldhausenStructure.K 0)
    (hy : KMap k.inclusion_exact 0 y = KMap hF 0 x) :
    ∃ z : h.waldhausenStructure.K 0, KMap h.inclusion_exact 0 z = x :=
  (h.KMap_mem_inclusion_range_iff k hF hp Dd De hsd hse x).mp ⟨y,hy⟩

include hp in
/-- Zero of the mapped actual object class detects source membership exactly. -/
theorem actual_zero_class (A : C) :
    h.classMap k hF (fun A ↦ (hp A).mp) (h.classOf A) = 0 ↔ P A :=
  (k.classOf_eq_zero_iff (F.obj A)).trans (hp A).symm

end General
end QuillenTest.GradedKZeroNaturality
