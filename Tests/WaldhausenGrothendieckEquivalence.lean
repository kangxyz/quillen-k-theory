/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.Functor

/-! Consumers of the full canonical general Waldhausen comparison retain the
original fine K₀, original grading inverse, all exact functors and original
object classes. No functorial factorization or cylinder data are present. -/
@[expose] public section

noncomputable section
open CategoryTheory Quillen.Waldhausen
universe u v
namespace Quillen.Tests.WaldhausenGrothendieckEquivalence
open AlgebraicGrothendieck
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (W : Structure C) (V : Structure D)

/-- The original realized grading inverse recovers every actual fine K₀ class. -/
theorem original_fine_round_trip (x : W.K 0) :
    grothendieckToKZero W (kZeroToGrothendieck W x) = x :=
  DFunLike.congr_fun (grothendieckToKZero_comp W) x

/-- Equality of arbitrary fine K₀ classes is detected by the original classical presentation. -/
theorem arbitrary_fine_class_detection (x y : W.K 0) :
    x = y ↔ kZeroToGrothendieck W x = kZeroToGrothendieck W y :=
  (kZeroToGrothendieck_injective W).eq_iff.symm

/-- The actual exact-functor kernel on all fine K₀ classes is detected by the
original exact-functor map on the classical weak-arrow/pushout presentation. -/
theorem arbitrary_fine_exact_kernel (F : C ⥤ D)
    (hF : IsExact W.cof W.weq V.cof V.weq F) (x : W.K 0) :
    KMap hF 0 x = 1 ↔
      (AlgebraicGrothendieck.map W F hF).toMultiplicative
        (kZeroToGrothendieck W x) = 1 := by
  rw [kZeroToGrothendieck_natural W V F hF x]
  constructor
  · intro h
    rw [h, map_one]
  · intro h
    apply kZeroToGrothendieck_injective V
    simpa only [map_one] using h

/-- Agreement on original object loops forces equality on every actual fine class. -/
theorem original_object_loops_determine_maps {H : Type v} [_root_.Group H]
    (f g : W.K 0 →* H) (h : ∀ A, f (W.kZeroObjectClass A) = g (W.kZeroObjectClass A)) :
    ∀ x : W.K 0, f x = g x := fun x ↦ DFunLike.congr_fun (kZero_hom_ext W f g h) x

/-- The bundled natural equivalence has exactly the original forward and inverse maps. -/
theorem original_bundled_components (M : SmallWaldhausenCategory.{u}) :
    SmallWaldhausenCategory.grothendieckKZeroIso.hom.app M =
      GrpCat.ofHom (grothendieckToKZero M.waldhausen) ∧
    SmallWaldhausenCategory.grothendieckKZeroIso.inv.app M =
      GrpCat.ofHom (kZeroToGrothendieck M.waldhausen) := ⟨rfl, rfl⟩

/-- The original canonical generator is retained by the full equivalence. -/
theorem original_object_under_equivalence (A : C) :
    grothendieckKZeroEquiv W (Multiplicative.ofAdd (objectClass W A)) =
      W.kZeroObjectClass A := grothendieckKZeroEquiv_objectClass W A

end Quillen.Tests.WaldhausenGrothendieckEquivalence
