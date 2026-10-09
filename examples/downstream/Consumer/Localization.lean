import Quillen.Localization.Serre.LocalizationTheorem
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Quillen
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Consumer
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

-- Use all three exactness positions with the canonical inclusion, quotient and boundary.
theorem inclusion_exact (n : ℕ) :
    (Devissage.KMap P n).range = (SerreLocalization.quotientKMap P n).ker :=
  SerreLocalization.inclusion_range_eq_quotient_ker P n

theorem quotient_exact (n : ℕ) :
    (SerreLocalization.quotientKMap P (n + 1)).range =
      (SerreLocalization.connectingHom P n).ker :=
  SerreLocalization.quotient_range_eq_connecting_ker P n

theorem boundary_exact (n : ℕ) :
    (SerreLocalization.connectingHom P n).range = (Devissage.KMap P n).ker :=
  SerreLocalization.connecting_range_eq_inclusion_ker P n

theorem quotient_zero_surjective : Function.Surjective (SerreLocalization.quotientKMap P 0) :=
  SerreLocalization.quotientKZero_surjective P
end Consumer
