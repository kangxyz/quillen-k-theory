/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.AlgebraicGeometry.PerfectComplexes.Bass.SupportedEnlargement

/-!
Twelve original-map consumers for supported Bass groups, genuine pair geometry, arbitrary pullback,
exact Laurent relations and unique descent, unchanged support-forgetting K0, old exact support
inclusion and all-degree enlargement laws.
-/
@[expose] public section

open Quillen.PerfectComplexes



noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace SupportedBassConsumers
open AlgebraicGeometry.Scheme Quillen.PerfectComplexes.Bass

/-- The polynomial vanishing open is the actual inverse-image open, with no qc-open premise. -/
theorem original_polynomial_support_square (A : QuasiCompactOpenPairs.{u}) :
    IsPullback ((AlgebraicGeometry.Scheme.Bass.pairPolynomialFunctor.obj A).obj.obj.hom)
      (pullback.fst (AlgebraicGeometry.Scheme.Products.toIntegerBase A.obj.obj.left)
        (AlgebraicGeometry.Scheme.PolynomialLaurent.polynomialProjection
          AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing))
      (pullback.fst (AlgebraicGeometry.Scheme.Products.toIntegerBase A.obj.obj.right)
        (AlgebraicGeometry.Scheme.PolynomialLaurent.polynomialProjection
          AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing))
          A.obj.obj.hom :=
  AlgebraicGeometry.Scheme.Bass.baseProductFunctor_map_isPullback _ _

/-- Both components of the genuine inverse-coordinate pair chart are open immersions. -/
theorem original_inverse_chart (A : QuasiCompactOpenPairs.{u}) :
    IsOpenImmersion (AlgebraicGeometry.Scheme.Bass.pairMinus.app A).hom.hom.left ∧
    IsOpenImmersion (AlgebraicGeometry.Scheme.Bass.pairMinus.app A).hom.hom.right := by
  change IsOpenImmersion ((AlgebraicGeometry.Scheme.Products.baseProductTransformation _ _
    (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentMinus
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing)
    (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentMinus_projection
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing)).app
      A.obj.obj.left) ∧
    IsOpenImmersion ((AlgebraicGeometry.Scheme.Products.baseProductTransformation _ _
    (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentMinus
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing)
    (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentMinus_projection
      AlgebraicGeometry.Scheme.PolynomialLaurent.Relative.integerRing)).app
      A.obj.obj.right)
  exact ⟨inferInstance,inferInstance⟩

/-- The original supported K0 pullback is retained on every commutative pair square. -/
theorem original_supported_Kzero {A B : QuasiCompactOpenPairs.{u}} (f : A ⟶ B)
    (a : PerfectSupportedK B.obj.obj.hom 0) :
    supportedNegativeKPullback f 0 (Additive.ofMul a) = Additive.ofMul (perfectSupportedKPullback f
      0 a) := rfl

/-- Arbitrary pair pullbacks compose in every original negative group. -/
theorem original_pair_composition {A B C : QuasiCompactOpenPairs.{u}}
    (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) (a : supportedNegativeK C n) :
    supportedNegativeKPullback (f ≫ g) n a =
      supportedNegativeKPullback f n (supportedNegativeKPullback g n a) := by
  rw [supportedNegativeKPullback_comp]
  rfl

/-- Every supported negative class is an original Laurent class with the exact chart relation. -/
theorem original_supported_presentation (A : QuasiCompactOpenPairs.{u}) (n : ℕ)
    (y : supportedNegativeK A (n+1)) :
    ∃ x : supportedNegativeK (AlgebraicGeometry.Scheme.Bass.pairLaurentFunctor.obj A) n,
      supportedNegativeKπ A n x = y ∧
      (y = 0 ↔ ∃ a b : supportedNegativeK (AlgebraicGeometry.Scheme.Bass.pairPolynomialFunctor.obj
        A) n,
        supportedNegativeKPullback (AlgebraicGeometry.Scheme.Bass.pairPlus.app A) n a -
          supportedNegativeKPullback (AlgebraicGeometry.Scheme.Bass.pairMinus.app A) n b = x) := by
  obtain ⟨x,rfl⟩ := supportedNegativeKπ_surjective A n y
  exact ⟨x,rfl,supportedNegativeKπ_eq_zero_iff A n x⟩

/-- A prescribed original Laurent homomorphism has exactly one quotient descent. -/
theorem original_supported_unique_descent (A : QuasiCompactOpenPairs.{u}) (n : ℕ)
    {B : AddCommGrpCat.{u+1}}
    (f : supportedNegativeK (AlgebraicGeometry.Scheme.Bass.pairLaurentFunctor.obj A) n ⟶ B)
    (hp : supportedNegativeKPullback (AlgebraicGeometry.Scheme.Bass.pairPlus.app A) n ≫ f = 0)
    (hm : supportedNegativeKPullback (AlgebraicGeometry.Scheme.Bass.pairMinus.app A) n ≫ f = 0) :
    ∃! g : supportedNegativeK A (n+1) ⟶ B, supportedNegativeKπ A n ≫ g = f :=
  ⟨supportedNegativeKDesc A n f hp hm,supportedNegativeKπ_desc A n f hp hm,
    fun g hg ↦ supportedNegativeKDesc_unique A n f hp hm g hg⟩

/-- The actual original support-forgetting K0 map is the recursion seed. -/
theorem original_forget_zero (A : QuasiCompactOpenPairs.{u}) (a : PerfectSupportedK A.obj.obj.hom 0)
  :
    supportedNegativeKForget A 0 (Additive.ofMul a) =
      Additive.ofMul (perfectSupportedKMap A.obj.obj.hom 0 a) := rfl

/-- Forgetting support retains the actual Laurent representative, with no auxiliary equivalence. -/
theorem original_forget_representative (A : QuasiCompactOpenPairs.{u}) (n : ℕ)
    (a : supportedNegativeK (AlgebraicGeometry.Scheme.Bass.pairLaurentFunctor.obj A) n) :
    supportedNegativeKForget A (n+1) (supportedNegativeKπ A n a) =
      negativeKπ (quasiCompactOpenPairsBase.obj A) n
        (supportedNegativeKForget (AlgebraicGeometry.Scheme.Bass.pairLaurentFunctor.obj A) n a) :=
  congrArg (fun g ↦ g a) (supportedNegativeKForget_π A n)

/-- Original arbitrary pair maps commute with support forgetting in every degree. -/
theorem original_forget_pair_square {A B : QuasiCompactOpenPairs.{u}} (f : A ⟶ B) (n : ℕ) :
    supportedNegativeKPullback f n ≫ supportedNegativeKForget A n =
      supportedNegativeKForget B n ≫ negativeKPullback (quasiCompactOpenPairsBase.map f) n :=
  supportedNegativeKForget_naturality f n

/-- Support enlargement starts at the original exact full-subcategory inclusion. -/
theorem original_support_inclusion (X : QuasiCompactSchemes.{u}) {U V : X.obj.Opens}
    (h : U ≤ V) (a : PerfectSupportedK V.ι 0) :
    supportedNegativeKEnlarge X h 0 (Additive.ofMul a) =
      Additive.ofMul (perfectSupportedChangeOpenKMap h 0 a) :=
  supportedNegativeKEnlarge_zero_original X h a

/-- Nested support enlargements compose even when none of the opens is qc. -/
theorem original_nested_support (X : QuasiCompactSchemes.{u}) {U V W : X.obj.Opens}
    (h : U ≤ V) (k : V ≤ W) (n : ℕ) :
    supportedNegativeKEnlarge X k n ≫ supportedNegativeKEnlarge X h n =
      supportedNegativeKEnlarge X (h.trans k) n := supportedNegativeKEnlarge_comp X h k n

/-- The absolute class of an original supported element survives every enlargement. -/
theorem original_support_absolute_class (X : QuasiCompactSchemes.{u}) {U V : X.obj.Opens}
    (h : U ≤ V) (n : ℕ)
    (a : supportedNegativeK (AlgebraicGeometry.Scheme.Bass.openSupportPair X V) n) :
    supportedNegativeKForget (AlgebraicGeometry.Scheme.Bass.openSupportPair X U) n
      (supportedNegativeKEnlarge X h n a) =
        supportedNegativeKForget (AlgebraicGeometry.Scheme.Bass.openSupportPair X V) n a :=
  congrArg (fun g ↦ g a) (supportedNegativeKEnlarge_forget X h n)

end SupportedBassConsumers

end
