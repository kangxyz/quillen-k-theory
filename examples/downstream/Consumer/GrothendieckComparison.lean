/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.KTheory.GrothendieckComparison.Functor

/-! An independent client detecting exact-functor K₀ kernels through the
original classical Grothendieck map, on arbitrary homotopical classes. -/
@[expose] public section

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Quillen
namespace Consumer.GrothendieckComparison
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  [Preadditive C] [HasFiniteBiproducts C] [Preadditive D] [HasFiniteBiproducts D]
  {E : ExactStructure C} {ED : ExactStructure D}

/-- Whether an arbitrary genuine K₀ class lies in an exact-functor kernel is
computed by the original map on the classical conflation presentation. -/
theorem exact_functor_kernel_iff (F : ExactFunctor E ED) (x : E.K 0) :
    F.KMap 0 x = 1 ↔
      F.grothendieckMap.toMultiplicative (E.kZeroToGrothendieck x) = 1 := by
  have hn := DFunLike.congr_fun F.kZeroToGrothendieck_naturality x
  change F.grothendieckMap.toMultiplicative (E.kZeroToGrothendieck x) =
    ED.kZeroToGrothendieck (F.KMap 0 x) at hn
  constructor
  · intro hx
    rw [hn, hx, map_one]
  · intro hx
    apply ED.grothendieckKZeroEquiv.symm.injective
    change ED.kZeroToGrothendieck (F.KMap 0 x) = ED.kZeroToGrothendieck 1
    rw [← hn, hx, map_one]

end Consumer.GrothendieckComparison
