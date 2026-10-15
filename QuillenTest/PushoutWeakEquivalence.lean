/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Affine.BassConeComparison

/-! Consumers check component coverage of the actual affine polynomial-chart pushout comparison,
homotopy extension at the unchanged perfect Bass cone point, and actual reverse-track cancellation
on every signed stable group. -/
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Quillen Quillen.LoopPrespectrum Quillen.PerfectComplexes
open AlgebraicGeometry.Scheme.PolynomialLaurent
open scoped Topology unitInterval
universe u
namespace QuillenTest.PushoutWeakEquivalence

open Quillen

/-- Every target component is covered by the actual two-polynomial-chart comparison. -/
theorem polynomialPushout_component_surjective (R : CommRingCat.{u}) (n : ℕ)
    (y : (HomotopyPushout.prespectrum (perfectFlatPrespectrumMap (polynomialProjection R))
      (perfectFlatPrespectrumMap (polynomialProjection R))).space (n + 1)) :
    ∃ x, Joined ((boundedFlatPerfectFlatPullbackPushoutMap (polynomialProjection R)
      (polynomialProjection R)).map (n + 1) x) y :=
  (boundedFlatPerfectFlatPullbackPushoutMap_positiveLevel_isWeakHomotopyEquivalence
    (polynomialProjection R) (polynomialProjection R) n).component_surjective y

/-- An arbitrary homotopy at the literal positive Bass cone point extends on its unchanged space. -/
theorem bassConePoint_extendsHomotopy (R : CommRingCat.{u}) (n : ℕ) (Z : TopCat.{u + 1})
    (p : C((mappingCone (bassSquareComparison R)).space (n + 1), Z))
    (H : C(unitInterval × PUnit.{u + 2}, Z))
    (hzero : ∀ a, H (0, a) = p ((mappingCone (bassSquareComparison R)).point (n + 1))) :
    ∃ K : C(unitInterval × (mappingCone (bassSquareComparison R)).space (n + 1), Z),
      (∀ x, K (0, x) = p x) ∧
      ∀ t a, K (t, (mappingCone (bassSquareComparison R)).point (n + 1)) = H (t, a) :=
  homotopyExtensionProperty_continuous (bassCone_positivePoint_homotopyExtensionProperty R n)
    Z p H hzero

/-- The actual reverse right-arrow track cancels on every original integer-graded stable group. -/
theorem rightReverseTrack_stable_cancellation
    {A B C : LoopPrespectrum.{u}} (f : A ⟶ B) {g g' : A ⟶ C}
    (H : Homotopy g g') (d : ℤ) :
    (stableHomotopyFunctor d).map (HomotopyPushout.rightHomotopyMap f H) ≫
      (stableHomotopyFunctor d).map (HomotopyPushout.rightHomotopyMap f H.symm) =
        𝟙 (stableHomotopyGroup (HomotopyPushout.prespectrum f g) d) := by
  rw [← Functor.map_comp]
  exact ((HomotopyPushout.rightHomotopyMapLeftHomotopy f H).stableHomotopyMap_eq d).trans
    ((stableHomotopyFunctor d).map_id _)

end QuillenTest.PushoutWeakEquivalence
