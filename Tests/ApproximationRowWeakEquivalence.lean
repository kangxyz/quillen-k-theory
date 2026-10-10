/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Waldhausen.Approximation.RowWeakEquivalence
public import Quillen.Waldhausen.SConstruction.Rows.WeakRealization
public import Quillen.Waldhausen.Functoriality.WeakKEquivalence

/-! Behavioral consumers retaining components, original maps, and canonical K-zero. -/
@[expose] public section

noncomputable section
open CategoryTheory Opposite
open scoped Simplicial
universe u v
namespace ApproximationRowWeakConsumers
open Quillen Quillen.Waldhausen Quillen.Waldhausen.QuotientRows

section Rows
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty]
  (J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W))
include h J

/-- Every actual target point in row zero has an original source point in its component. -/
theorem row_zero_component_surjective (y : |(weakRowNerve V).obj (op ⦋0⦌)|) :
    ∃ x, Joined (SSet.toTop.map ((weakRowNerveMap W V hF).app (op ⦋0⦌)) x) y :=
  (h.weakRowNerveMap_row_isWeakHomotopyEquivalence hF J 0).component_surjective y

/-- All finite homotopy sets are carried bijectively by the actual original row map. -/
theorem original_row_homotopy_map_bijective (n k : ℕ) (x : |(weakRowNerve W).obj (op ⦋n⦌)|) :
    Function.Bijective (homotopyGroupMap (N := Fin k)
      (SSet.toTop.map ((weakRowNerveMap W V hF).app (op ⦋n⦌))).hom (x := x) rfl) :=
  (h.weakRowNerveMap_row_isWeakHomotopyEquivalence hF J n).homotopy_bijective x k

end Rows
section Transport
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (hF : IsExact W.cof W.weq V.cof V.weq F)

/-- The original grid presentation keeps the source and target component comparison. -/
theorem original_delooping_component_surjective
    (h : IsWeakHomotopyEquivalence
      (SSet.toTop.map (TheoremA.diagonalMap (weakRowNerveMap W V hF))).hom)
    (y : V.Delooping) : ∃ x, Joined (deloopingMap hF x) y :=
  (deloopingMap_isWeakHomotopyEquivalence_of_weakRowDiagonal hF h).component_surjective y

/-- Complete weakness is retained by the exact canonical normalization used by KMap. -/
theorem rebased_component_surjective
    (h : IsWeakHomotopyEquivalence (deloopingMap hF).hom) (y : V.Delooping) :
    ∃ x, Joined (deloopingMap hF.rebase x) y :=
  (rebasedDeloopingMap_isWeakHomotopyEquivalence hF h).component_surjective y

/-- K-zero is included by the original canonical group map. -/
theorem original_K_zero_bijective
    (h : IsWeakHomotopyEquivalence (deloopingMap hF).hom) :
    Function.Bijective (KMap hF 0) := KMap_bijective_of_isWeakHomotopyEquivalence hF h 0

/-- The group-equivalence forward function is exactly the unchanged canonical map. -/
theorem original_K_forward
    (h : IsWeakHomotopyEquivalence (deloopingMap hF).hom) (n : ℕ) (a : W.K n) :
    KEquivOfWeakRealization hF h n a = KMap hF n a := rfl

/-- The inverse really is a right inverse for that original canonical homomorphism. -/
theorem original_K_right_inverse
    (h : IsWeakHomotopyEquivalence (deloopingMap hF).hom) (n : ℕ) (a : V.K n) :
    KMap hF n ((KEquivOfWeakRealization hF h n).symm a) = a :=
  (KEquivOfWeakRealization hF h n).apply_symm_apply a

end Transport
end ApproximationRowWeakConsumers
