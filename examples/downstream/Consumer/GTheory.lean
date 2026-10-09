import Quillen.GTheory.FiniteModules.LocalizationSequence
noncomputable section
universe u
open Quillen

namespace Consumer
variable {R : Type u} [CommRing R] [IsNoetherianRing R] (S : Submonoid R)

-- Genuine finite-module G-theory, with no supplied fiber-comparison hypothesis.
def scalarLocalization (n : ℕ) :
    FiniteModuleLocalization.G R n →* FiniteModuleLocalization.G (Localization S) n :=
  FiniteModuleLocalization.localizationKMap S n

theorem scalar_localization_exact (n : ℕ) :
    (FiniteModuleLocalization.supportedKMap S n).range = (scalarLocalization S n).ker :=
  FiniteModuleLocalization.supported_range_eq_localization_ker S n

theorem scalar_localization_zero_surjective : Function.Surjective (scalarLocalization S 0) :=
  FiniteModuleLocalization.localizationKZero_surjective S

-- A concrete noetherian ring, rather than only an abstract parameterized theorem.
abbrev integerGZeroGroup : Group (FiniteModuleLocalization.G ℤ 0) := inferInstance

theorem integer_two_localization_zero_surjective : Function.Surjective
    (FiniteModuleLocalization.localizationKMap (Submonoid.powers (2 : ℤ)) 0) :=
  FiniteModuleLocalization.localizationKZero_surjective (Submonoid.powers (2 : ℤ))
end Consumer
