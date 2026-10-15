/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.ClassicalMap

/-! Consumers of the canonical classical-to-fine comparison retain the original
object classes and displayed cofibers. Arbitrary-class statements distinguish
the proved splitting from the remaining generation of all fine K₀ classes. -/
@[expose] public section

open Quillen.Waldhausen


noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace QuillenTest.WaldhausenClassicalMap

open Quillen
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (W : Structure C) (V : Structure D)

/-- Original classical classes are recovered exactly after passage to actual fine K₀. -/
theorem original_classical_round_trip (a : Multiplicative (AlgebraicGrothendieck.Group W)) :
    AlgebraicGrothendieck.kZeroToGrothendieck W
      (AlgebraicGrothendieck.grothendieckToKZero W a) = a :=
  DFunLike.congr_fun (AlgebraicGrothendieck.kZeroToGrothendieck_comp W) a

/-- Every original displayed cofiber gives its difference relation in actual fine K₀. -/
theorem displayed_cofiber_difference {A B Q : C} {i : A ⟶ B} {q : B ⟶ Q}
    (hi : W.cof i) (hQ : IsPushout i (W.isZero.from_ A) q (W.isZero.to_ Q)) :
    W.kZeroObjectClass B * (W.kZeroObjectClass A)⁻¹ = W.kZeroObjectClass Q := by
  let : CommGroup (W.K 0) := Additivity.KCommGroup W 0
  rw [W.kZeroObjectClass_cofiber hi hQ]
  simp [mul_comm, mul_left_comm]

/-- The original exact-functor map preserves the canonical image of every classical class. -/
theorem arbitrary_classical_naturality (F : C ⥤ D)
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (a : Multiplicative (AlgebraicGrothendieck.Group W)) :
    KMap hF 0 (AlgebraicGrothendieck.grothendieckToKZero W a) =
      AlgebraicGrothendieck.grothendieckToKZero V
        ((AlgebraicGrothendieck.map W F hF).toMultiplicative a) :=
  DFunLike.congr_fun (AlgebraicGrothendieck.grothendieckToKZero_natural W V F hF) a

/-- The actual exact-functor kernel on the full classical image is detected by
precisely the original classical functor map. -/
theorem classical_image_kernel_iff (F : C ⥤ D)
    (hF : IsExact W.cof W.weq V.cof V.weq F)
    (a : Multiplicative (AlgebraicGrothendieck.Group W)) :
    KMap hF 0 (AlgebraicGrothendieck.grothendieckToKZero W a) = 1 ↔
      (AlgebraicGrothendieck.map W F hF).toMultiplicative a = 1 := by
  rw [arbitrary_classical_naturality W V F hF a,
    ← (AlgebraicGrothendieck.grothendieckToKZero V).map_one]
  exact (AlgebraicGrothendieck.grothendieckToKZero_injective V).eq_iff

/-- On an arbitrary fine K₀ class, the proved round trip is an idempotent projection. -/
theorem fine_round_trip_idempotent (x : W.K 0) :
    AlgebraicGrothendieck.grothendieckToKZero W
      (AlgebraicGrothendieck.kZeroToGrothendieck W
        (AlgebraicGrothendieck.grothendieckToKZero W
          (AlgebraicGrothendieck.kZeroToGrothendieck W x))) =
      AlgebraicGrothendieck.grothendieckToKZero W
        (AlgebraicGrothendieck.kZeroToGrothendieck W x) := by
  rw [original_classical_round_trip]

/-- The exact original object-loop classes belong to the image of the canonical comparison. -/
theorem original_object_in_image (A : C) :
    W.kZeroObjectClass A ∈ Set.range (AlgebraicGrothendieck.grothendieckToKZero W) :=
  ⟨Multiplicative.ofAdd (AlgebraicGrothendieck.objectClass W A),
    AlgebraicGrothendieck.grothendieckToKZero_objectClass W A⟩

end QuillenTest.WaldhausenClassicalMap
