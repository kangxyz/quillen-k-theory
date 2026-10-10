/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Approximation.KEquivalence
import Quillen.Waldhausen.SmallModel.Approximation

/-! # Original S/K approximation with independent object and hom universes

The actual approximation and joint-cylinder data pass to the existing
common-universe model. Its proved approximation conclusion then transfers
back through the strictly natural original S-homeomorphism square. The
original realization map and canonical K-homomorphism remain unchanged.
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.Waldhausen
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}

namespace HasApproximationProperty
variable (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty]
  (J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W))
include h J

/-- Approximation for the original realization with independent object and
morphism universes, retaining the actual exact functor and map. -/
theorem deloopingMap_isWeakHomotopyEquivalence_general :
    IsWeakHomotopyEquivalence (deloopingMap hF).hom :=
  deloopingMap_isWeakHomotopyEquivalence_of_smallModel hF
    (h.smallModel.deloopingMap_isWeakHomotopyEquivalence hF.smallModel J.reflexiveSmallModel)

/-- The original canonical K-map is bijective for arbitrary object/hom universes. -/
theorem KMap_bijective_general (n : ℕ) : Function.Bijective (Waldhausen.KMap hF n) :=
  KMap_bijective_of_isWeakHomotopyEquivalence hF
    (deloopingMap_isWeakHomotopyEquivalence_general h hF J) n

/-- The two-universe approximation equivalence retains the original canonical K-map. -/
def KEquivGeneral (n : ℕ) : W.K n ≃* V.K n :=
  MulEquiv.ofBijective (Waldhausen.KMap hF n) (KMap_bijective_general h hF J n)

/-- The equivalence retains the literal original canonical K-homomorphism. -/
@[simp] theorem KEquivGeneral_toMonoidHom (n : ℕ) :
    (KEquivGeneral h hF J n).toMonoidHom = Waldhausen.KMap hF n := rfl

end HasApproximationProperty
end Quillen.Waldhausen
