/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.GTheory.FiniteModules.SmallModelLocalization
public import Quillen.Localization.Serre.LocalizationTarget

/-!
# Connective G-localization for a commutative noetherian ring

The sequence below uses the actual finite-module localization and its original
canonical small-model K-map. Its supported term is the full Serre subcategory
of the small model whose represented finite modules become zero after scalar
localization. For powers of one element, these are precisely modules uniformly
annihilated by a power of that element.
-/
@[expose] public section


noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts
namespace Quillen.FiniteModuleLocalization

private theorem exact_transport
    {A B C A' B' C' : Type u}
    [Group A] [Group B] [Group C] [Group A'] [Group B'] [Group C']
    (i : A →* B) (f : B →* C) (i' : A' →* B') (f' : B' →* C')
    (eA : A ≃* A') (eB : B ≃* B') (eC : C ≃* C')
    (hi : ∀ a, eB (i a) = i' (eA a))
    (hf : ∀ b, eC (f b) = f' (eB b))
    (h : i'.range = f'.ker) : i.range = f.ker := by
  ext b
  rw [MonoidHom.mem_range, MonoidHom.mem_ker]
  constructor
  · rintro ⟨a, rfl⟩
    apply eC.injective
    rw [map_one, hf, hi]
    have hx : i' (eA a) ∈ i'.range := ⟨eA a, rfl⟩
    rw [h] at hx
    exact hx
  · intro hb
    have hx : eB b ∈ i'.range := by
      rw [h]
      change f' (eB b) = 1
      rw [← hf, hb, map_one]
    obtain ⟨a, ha⟩ := hx
    refine ⟨eA.symm a, eB.injective ?_⟩
    rw [hi, eA.apply_symm_apply, ha]

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (S : Submonoid R)

/-- Finite-module G-theory in the actual chosen small model. -/
abbrev G (A : Type u) [CommRing A] [IsNoetherianRing A] (n : ℕ) :=
  (CoherentScheme.finiteModuleExactStructure.{u, u} A).SmallK n

/-- The supported G-term, formed from the genuine Serre kernel on the small model. -/
abbrev SupportedG (n : ℕ) := (Devissage.subcategoryExactStructure (smallTorsion S)).K n

/-- The canonical scalar-localization map. -/
def localizationKMap (n : ℕ) : G R n →* G (Localization S) n :=
  (exactFunctor S).smallKMap n

/-- The supported inclusion, through the canonical identity exact-structure comparison. -/
def supportedKMap (n : ℕ) : SupportedG S n →* G R n :=
  (smallAbelianKEquiv R n).symm.toMonoidHom.comp (Devissage.KMap (smallTorsion S) n)

/-- The actual localization boundary, transported from the canonical Serre
path-space boundary through the proved target equivalences. -/
def connectingHom (n : ℕ) : G (Localization S) (n + 1) →* SupportedG S n :=
  (SerreLocalization.actualConnectingHom (smallTorsion S) (smallFunctor S) n).comp
    (smallAbelianKEquiv (Localization S) (n + 1)).toMonoidHom

lemma localizationKMap_comparison (n : ℕ) (x : G R n) :
    smallAbelianKEquiv (Localization S) n (localizationKMap S n x) =
      SerreLocalization.KMap (smallTorsion S) (smallFunctor S) n (smallAbelianKEquiv R n x) := by
  exact DFunLike.congr_fun (smallKMap_comparison S n) x

/-- Exactness at G_n(R), for every nonnegative n. -/
theorem supported_range_eq_localization_ker (n : ℕ) :
    (supportedKMap S n).range = (localizationKMap S n).ker := by
  apply exact_transport (supportedKMap S n) (localizationKMap S n)
    (Devissage.KMap (smallTorsion S) n)
    (SerreLocalization.KMap (smallTorsion S) (smallFunctor S) n)
    (MulEquiv.refl _) (smallAbelianKEquiv R n) (smallAbelianKEquiv (Localization S) n)
  · intro a
    exact (smallAbelianKEquiv R n).apply_symm_apply _
  · exact localizationKMap_comparison S n
  · exact SerreLocalization.actual_inclusion_range_eq_KMap_ker (smallTorsion S) (smallFunctor S) n

/-- Exactness at G_(n+1)(S⁻¹R), using the actual localization homomorphism. -/
theorem localization_range_eq_connecting_ker (n : ℕ) :
    (localizationKMap S (n + 1)).range = (connectingHom S n).ker := by
  apply exact_transport (localizationKMap S (n + 1)) (connectingHom S n)
    (SerreLocalization.KMap (smallTorsion S) (smallFunctor S) (n + 1))
    (SerreLocalization.actualConnectingHom (smallTorsion S) (smallFunctor S) n)
    (smallAbelianKEquiv R (n + 1)) (smallAbelianKEquiv (Localization S) (n + 1))
    (MulEquiv.refl _)
  · exact localizationKMap_comparison S (n + 1)
  · intro a; rfl
  · exact SerreLocalization.actual_KMap_range_eq_connecting_ker (smallTorsion S) (smallFunctor S) n

/-- Exactness at the supported term G_n, including degree zero. -/
theorem connecting_range_eq_supported_ker (n : ℕ) :
    (connectingHom S n).range = (supportedKMap S n).ker := by
  apply exact_transport (connectingHom S n) (supportedKMap S n)
    (SerreLocalization.actualConnectingHom (smallTorsion S) (smallFunctor S) n)
    (Devissage.KMap (smallTorsion S) n)
    (smallAbelianKEquiv (Localization S) (n + 1)) (MulEquiv.refl _)
    (smallAbelianKEquiv R n)
  · intro a; rfl
  · intro a
    exact (smallAbelianKEquiv R n).apply_symm_apply _
  · exact SerreLocalization.actual_connecting_range_eq_inclusion_ker (smallTorsion S) (smallFunctor
    S) n

/-- The connective sequence ends in the genuine homotopical G₀ surjection. -/
theorem localizationKZero_surjective : Function.Surjective (localizationKMap S 0) := by
  intro y
  obtain ⟨x, hx⟩ := SerreLocalization.actualKZero_surjective (smallTorsion S) (smallFunctor S)
    (smallAbelianKEquiv (Localization S) 0 y)
  refine ⟨(smallAbelianKEquiv R 0).symm x, (smallAbelianKEquiv (Localization S) 0).injective ?_⟩
  rw [localizationKMap_comparison, MulEquiv.apply_symm_apply, hx]

/-- The complete connective G-localization theorem for finite modules over a
commutative noetherian ring, with its actual localization map. -/
theorem localization_longExact :
    (∀ n, (supportedKMap S n).range = (localizationKMap S n).ker) ∧
    (∀ n, (localizationKMap S (n + 1)).range = (connectingHom S n).ker) ∧
    (∀ n, (connectingHom S n).range = (supportedKMap S n).ker) ∧
    Function.Surjective (localizationKMap S 0) :=
  ⟨supported_range_eq_localization_ker S, localization_range_eq_connecting_ker S,
    connecting_range_eq_supported_ker S, localizationKZero_surjective S⟩

end Quillen.FiniteModuleLocalization
