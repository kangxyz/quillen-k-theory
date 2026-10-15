/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.ExactCategory.Abelian
public import Quillen.CategoryTheory.TheoremB.StructuredWeakComparison
public import Quillen.Localization.Serre.StructuredTransitions
public import Quillen.Localization.Serre.LocalizationEndpoint

/-!
# The canonical connective Serre localization sequence

For a small abelian category and a Serre class, the actual canonical based
comparison from the Serre subcategory's Q-space to the quotient map's
path-space homotopy fiber is bijective on every homotopy set, including π₀.
Theorem B's structured transitions are proved for the actual Serre quotient;
no comparison, cartesian-square, filtration, or quotient hypothesis is added.

The resulting sequence uses precisely the canonical inclusion and quotient
K-maps, with the boundary obtained from the actual path-space boundary.
All three recurring positions are exact in every nonnegative degree, and
the sequence terminates in the canonical surjection onto homotopical K₀.
The comparison theorem here is weak: no global homotopy inverse is claimed.
-/
@[expose] public section

open CategoryTheory.ExactCategory



noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits

namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- The actual normalized Serre comparison is bijective in every homotopy
degree, including π₀, under only the abelian and Serre-class assumptions. -/
theorem basedLocalizationFiberComparison_bijective (n : ℕ) :
    Function.Bijective (homotopyGroupMap (N := Fin n)
      (basedLocalizationFiberComparison P) (basedLocalizationFiberComparison_basepoint P)) :=
  basedLocalizationFiberComparison_bijective_of_structured P n
    (TheoremB.structuredFiberComparison_bijective (quotientNormalizedQ P)
      (normalizedQuotient_structuredTransitions P
        (quotientStructuredTransitionHomotopyEquivalences P))
      (abelianExactStructure C).qZero n)

/-- The canonical comparison homomorphism is bijective in each K-degree. -/
theorem localizationFiberComparisonHom_bijective (n : ℕ) :
    Function.Bijective (localizationFiberComparisonHom P n) :=
  basedLocalizationFiberComparison_bijective P (n + 1)

/-- The canonical comparison, promoted to a group isomorphism without
changing its forward homomorphism. -/
def localizationFiberEquiv (n : ℕ) :
    (CategoryTheory.ObjectProperty.subcategoryExactStructure P).K n ≃*
      HomotopyGroup.Pi (n + 1) (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P) :=
  localizationFiberEquivOfBijective P n (localizationFiberComparisonHom_bijective P n)

/-- The underlying monoid homomorphism of this K-equivalence. -/
@[simp] theorem localizationFiberEquiv_coe (n : ℕ) :
    (↑(localizationFiberEquiv P n) : (CategoryTheory.ObjectProperty.subcategoryExactStructure P).K n
      →*
        HomotopyGroup.Pi (n + 1) (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P)) =
        localizationFiberComparisonHom P n := rfl


/-- The localization boundary Kₙ₊₁(C/P) → Kₙ(P), obtained from the actual
path-space connecting homomorphism and the canonical comparison inverse. -/
def connectingHom (n : ℕ) :
    (quotientExactStructure P).K (n + 1) →* (CategoryTheory.ObjectProperty.subcategoryExactStructure
      P).K n :=
  connectingHomOfComparison P n (localizationFiberEquiv P n)

/-- The boundary is identified with the genuine path-space boundary by
the canonical comparison, including at K₁(C/P) → K₀(P). -/
theorem comparison_comp_connectingHom (n : ℕ) :
    (localizationFiberComparisonHom P n).comp (connectingHom P n) =
      fiberConnectingHom P n :=
  comparison_comp_connectingHomOfComparison P n _ rfl

/-- Exactness at Kₙ(C), for every n ≥ 0. -/
theorem inclusion_range_eq_quotient_ker (n : ℕ) :
    (Devissage.KMap P n).range = (quotientKMap P n).ker :=
  inclusion_range_eq_quotient_ker_of_comparison_surjective P n
    (localizationFiberComparisonHom_bijective P n).surjective

/-- Exactness at Kₙ₊₁(C/P), for every n ≥ 0. -/
theorem quotient_range_eq_connecting_ker (n : ℕ) :
    (quotientKMap P (n + 1)).range = (connectingHom P n).ker :=
  quotient_range_eq_connecting_ker_of_comparison P n (localizationFiberEquiv P n)

/-- Exactness at Kₙ(P), for every n ≥ 0. -/
theorem connecting_range_eq_inclusion_ker (n : ℕ) :
    (connectingHom P n).range = (Devissage.KMap P n).ker :=
  connecting_range_eq_inclusion_ker_of_comparison P n (localizationFiberEquiv P n) rfl

/-- The connective tail ends with K₀(C) → K₀(C/P) → 0. This uses
connectedness of BQ and the actual fiber comparison on π₀, without an
additional Grothendieck-group presentation hypothesis. -/
theorem quotientKZero_surjective : Function.Surjective (quotientKMap P 0) :=
  quotientKZero_surjective_of_comparison_piZero_surjective P
    (basedLocalizationFiberComparison_bijective P 0).surjective

/-- The complete canonical localization sequence, with all exactness
positions and the terminal K₀ surjection bundled. -/
def localizationSequence : KLocalizationSequence P :=
  localizationSequenceOfComparison P (basedLocalizationFiberComparison_bijective P)

@[simp] theorem localizationSequence_connecting (n : ℕ) :
    (localizationSequence P).connecting n = connectingHom P n := rfl

/-- Quillen localization for small abelian categories and Serre classes:
all three recurring exactness positions and the connective K₀ endpoint. -/
theorem localization_longExact :
    (∀ n, (Devissage.KMap P n).range = (quotientKMap P n).ker) ∧
    (∀ n, (quotientKMap P (n + 1)).range = (connectingHom P n).ker) ∧
    (∀ n, (connectingHom P n).range = (Devissage.KMap P n).ker) ∧
    Function.Surjective (quotientKMap P 0) :=
  ⟨inclusion_range_eq_quotient_ker P, quotient_range_eq_connecting_ker P,
    connecting_range_eq_inclusion_ker P, quotientKZero_surjective P⟩

/-- The low-degree tail K₁(C) → K₁(C/P) → K₀(P) → K₀(C) → K₀(C/P) → 0,
using the same canonical maps as the full sequence. -/
theorem localization_KZero_tail :
    (quotientKMap P 1).range = (connectingHom P 0).ker ∧
    (connectingHom P 0).range = (Devissage.KMap P 0).ker ∧
    (Devissage.KMap P 0).range = (quotientKMap P 0).ker ∧
    Function.Surjective (quotientKMap P 0) :=
  ⟨quotient_range_eq_connecting_ker P 0,
    connecting_range_eq_inclusion_ker P 0,
    inclusion_range_eq_quotient_ker P 0, quotientKZero_surjective P⟩
end Quillen.SerreLocalization
