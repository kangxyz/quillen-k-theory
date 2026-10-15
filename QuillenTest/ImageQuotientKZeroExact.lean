/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.GrothendieckComparison.ImageQuotientExact

/-! # Original-map consumers of image-quotient K-zero exactness -/
@[expose] public section

open Quillen.Waldhausen


noncomputable section
open CategoryTheory
open Quillen.Waldhausen.AlgebraicGrothendieck
universe u v
namespace QuillenTest.ImageQuotientKZeroExact

open Quillen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (W : Structure C) {V : Structure D} (F : C ⥤ D)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  (T : FunctorialFactorization V.smallModel)

include T

/-- Kernel membership gives an actual preimage under the original exact-functor KMap. -/
theorem original_kernel_preimage (x : V.K 0)
    (hx : KMap (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested) 0 x = 1) :
    ∃ a : W.K 0, KMap hF 0 a = x := by
  have hm : x ∈ (KMap hF 0).range := by
    rw [imageQuotient_changeWeakKMap_range_ker W F hF T]
    exact hx
  exact hm

/-- The literal coarse class lifts under the unchanged changeWeak KMap. -/
theorem original_coarse_preimage (y : (imageQuotientGrading W F hF).coarseStructure.K 0) :
    ∃ x : V.K 0,
      KMap (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested) 0 x = y :=
  imageQuotient_changeWeakKMap_surjective W F hF T y

/-- Every original exact-functor image dies under the actual changeWeak map. -/
theorem original_image_zero (a : W.K 0) :
    KMap (Fibration.changeWeak_exact (imageQuotientGrading W F hF).nested) 0
      (KMap hF 0 a) = 1 := by
  have hm : KMap hF 0 a ∈ (KMap hF 0).range := ⟨a, rfl⟩
  rw [imageQuotient_changeWeakKMap_range_ker W F hF T] at hm
  exact hm

end QuillenTest.ImageQuotientKZeroExact
