/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Waldhausen.Approximation.RowWeakEquivalence
import Quillen.Waldhausen.SConstruction.Rows.WeakRealization
import Quillen.Waldhausen.Functoriality.WeakKEquivalence
import Quillen.Topology.Realization.BisimplicialWeakEquivalence

/-! # Approximation for the original S-realization and connective K-map

Original App1/App2, exactness, target two-out-of-three, and structural exact
source joint-cylinder data imply complete weakness of the original S-map
and bijectivity of the canonical K-map in every nonnegative degree.

The row conditions are proved by genuine finite-flag lifting, quotient
descent and source factorization. Complete row weakness follows from actual
finite-poset comma cones and the poset-resolution argument. The weak
diagonal theorem retains the original map, and canonical zero rebasing is
handled by its actual natural-isomorphism homotopy.
-/
noncomputable section
open CategoryTheory
universe u
namespace Quillen.Waldhausen.HasApproximationProperty
variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  {W : Structure C} {V : Structure D} {F : C ⥤ D}
  (h : HasApproximationProperty W V F)
  (hF : IsExact W.cof W.weq V.cof V.weq F)
  [V.weq.HasTwoOutOfThreeProperty]
  (J : Fibration.RowFactorization.JointData (Fibration.NestedWeakEquivalences.refl W))
include h J

/-- The original exact S-construction map is a complete weak equivalence.
The given joint-cylinder data is structural base data, not a row or
realization lifting assumption. -/
theorem deloopingMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (deloopingMap hF).hom :=
  QuotientRows.deloopingMap_isWeakHomotopyEquivalence_of_weakRowDiagonal hF
    (BisimplicialRealization.diagonalMap_isRealizationWeakEquivalence
      (QuotientRows.weakRowNerveMap W V hF)
      (weakRowNerveMap_row_isWeakHomotopyEquivalence h hF J))

/-- The actual original canonical K-map is bijective in all connective degrees,
including K-zero, under the stated genuine approximation and cylinder inputs. -/
theorem KMap_bijective (n : ℕ) : Function.Bijective (Waldhausen.KMap hF n) :=
  KMap_bijective_of_isWeakHomotopyEquivalence hF
    (deloopingMap_isWeakHomotopyEquivalence h hF J) n

/-- Approximation as an actual group equivalence, with the original canonical
K-homomorphism as its prescribed forward map. -/
def KEquiv (n : ℕ) : W.K n ≃* V.K n :=
  MulEquiv.ofBijective (Waldhausen.KMap hF n) (KMap_bijective h hF J n)

/-- The resulting group equivalence retains the literal original K-map. -/
@[simp] theorem KEquiv_toMonoidHom (n : ℕ) :
    (KEquiv h hF J n).toMonoidHom = Waldhausen.KMap hF n := rfl

end Quillen.Waldhausen.HasApproximationProperty
