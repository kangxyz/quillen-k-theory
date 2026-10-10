/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/

module

public import Quillen.Localization.Serre.StructuredComparisonWeak

/-!
# Exact-sequence packaging for the canonical Serre comparison

This module contains only transport: its all-degree comparison-bijectivity
hypothesis is explicit. The localization theorem must discharge that hypothesis
from the abelian and Serre assumptions. The maps in the resulting sequence are
the existing exact inclusion and quotient K-maps, and the boundary is the
actual path-space boundary transported through the canonical comparison.
-/
@[expose] public section


noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- All three positions of the connective localization sequence, with the
inclusion and quotient homomorphisms fixed to the canonical K-maps. The last
field is the terminal surjection onto homotopical K₀. -/
structure KLocalizationSequence where
  /-- The boundary homomorphism from degree `n + 1` K-theory of the Serre quotient to degree `n`
  K-theory of the Serre subcategory, compatible with the specified fiber comparison. -/
  connecting : ∀ n : ℕ,
    (quotientExactStructure P).K (n + 1) →* (Devissage.subcategoryExactStructure P).K n
  comparison_connecting : ∀ n,
    (localizationFiberComparisonHom P n).comp (connecting n) = fiberConnectingHom P n
  exact_ambient : ∀ n,
    (Devissage.KMap P n).range = (quotientKMap P n).ker
  exact_quotient : ∀ n,
    (quotientKMap P (n + 1)).range = (connecting n).ker
  exact_subcategory : ∀ n,
    (connecting n).range = (Devissage.KMap P n).ker
  surjective_KZero : Function.Surjective (quotientKMap P 0)

/-- A proved bijective canonical comparison gives its unique group
isomorphism; the forward map is unchanged. -/
def localizationFiberEquivOfBijective (n : ℕ)
    (h : Function.Bijective (localizationFiberComparisonHom P n)) :
    (Devissage.subcategoryExactStructure P).K n ≃*
      HomotopyGroup.Pi (n + 1) (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P) :=
  MulEquiv.ofBijective (localizationFiberComparisonHom P n) h

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem localizationFiberEquivOfBijective_coe (n : ℕ)
    (h : Function.Bijective (localizationFiberComparisonHom P n)) :
    (↑(localizationFiberEquivOfBijective P n h) : (Devissage.subcategoryExactStructure P).K n →*
        HomotopyGroup.Pi (n + 1) (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P)) =
      localizationFiberComparisonHom P n := rfl


/-- Transporting the actual connecting map through the canonical comparison
retains its defining equation, rather than choosing an unrelated exact map. -/
theorem comparison_comp_connectingHomOfComparison (n : ℕ)
    (e : (Devissage.subcategoryExactStructure P).K n ≃*
      HomotopyGroup.Pi (n + 1) (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P))
    (he : e.toMonoidHom = localizationFiberComparisonHom P n) :
    (localizationFiberComparisonHom P n).comp (connectingHomOfComparison P n e) =
      fiberConnectingHom P n := by
  rw [← he]
  ext a
  exact e.apply_symm_apply (fiberConnectingHom P n a)

/-- Every degree, including degree zero, of the genuine based comparison
suffices for the complete canonical connective K-theory sequence. This is a
conditional adapter, not the geometric localization theorem. -/
def localizationSequenceOfComparison
    (h : ∀ n : ℕ, Function.Bijective (homotopyGroupMap (N := Fin n)
      (basedLocalizationFiberComparison P) (basedLocalizationFiberComparison_basepoint P))) :
    KLocalizationSequence P where
  connecting n := connectingHomOfComparison P n
    (localizationFiberEquivOfBijective P n (h (n + 1)))
  comparison_connecting n := comparison_comp_connectingHomOfComparison P n _ rfl
  exact_ambient n := inclusion_range_eq_quotient_ker_of_comparison_surjective P n
    (h (n + 1)).surjective
  exact_quotient n := quotient_range_eq_connecting_ker_of_comparison P n _
  exact_subcategory n := connecting_range_eq_inclusion_ker_of_comparison P n _ rfl
  surjective_KZero := quotientKZero_surjective_of_comparison_piZero_surjective P
    (h 0).surjective

/-- The transported boundary is uniquely determined by the canonical
comparison equation whenever the comparison is injective. -/
theorem connecting_unique_of_comparison_injective (n : ℕ)
    (h : Function.Injective (localizationFiberComparisonHom P n))
    (δ δ' : (quotientExactStructure P).K (n + 1) →*
      (Devissage.subcategoryExactStructure P).K n)
    (hδ : (localizationFiberComparisonHom P n).comp δ = fiberConnectingHom P n)
    (hδ' : (localizationFiberComparisonHom P n).comp δ' = fiberConnectingHom P n) :
    δ = δ' := by
  ext a
  apply h
  exact DFunLike.congr_fun (hδ.trans hδ'.symm) a

end Quillen.SerreLocalization
