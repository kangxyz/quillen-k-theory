/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Fibration.Rows.CoarseJoint
public import Quillen.Waldhausen.Approximation.GeneralKEquivalence
public import Quillen.Waldhausen.Approximation.WeakCommaCylinder

/-! # Approximation from an actual fine joint cylinder with coarse-weak projection

App1 and exactness reflect target saturation to the actual source weak
class. The original fine joint cylinder then becomes genuinely coarse-exact
by gluing and its projection squares. This supplies the structural input of
approximation on the enlarged source weak model, with all original maps.
-/
@[expose] public section

noncomputable section
open CategoryTheory
universe u v
namespace Quillen.Waldhausen.Fibration
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (N : NestedWeakEquivalences W) (J : RowFactorization.JointData N)
  (h : HasApproximationProperty N.coarse V F)
  (hF : IsExact N.coarse.cof N.coarse.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty]
include J h

/-- The unchanged coarse-source S-map is a complete weak equivalence, using
only honest fine joint data with its given coarse-weak projection. Source
saturation follows from the original App1 and target saturation. -/
theorem coarse_deloopingMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (deloopingMap hF).hom := by
  let : N.coarse.weq.HasTwoOutOfThreeProperty := h.source_twoOutOfThree hF
  exact h.deloopingMap_isWeakHomotopyEquivalence_general hF (J.coarseReflexive N)

/-- The actual original coarse-source canonical K-map is bijective in every degree. -/
theorem coarse_KMap_bijective (n : ℕ) : Function.Bijective (KMap hF n) :=
  KMap_bijective_of_isWeakHomotopyEquivalence hF
    (coarse_deloopingMap_isWeakHomotopyEquivalence N J h hF) n

/-- The coarse-source approximation equivalence has the original canonical K-map forward. -/
def coarseKEquiv (n : ℕ) : N.coarse.K n ≃* V.K n :=
  MulEquiv.ofBijective (KMap hF n) (coarse_KMap_bijective N J h hF n)

/-- The coarse approximation equivalence retains the original canonical K-homomorphism. -/
@[simp] theorem coarseKEquiv_coe (n : ℕ) :
    (↑(coarseKEquiv N J h hF n) : N.coarse.K n →* V.K n) = KMap hF n := rfl


end Quillen.Waldhausen.Fibration
