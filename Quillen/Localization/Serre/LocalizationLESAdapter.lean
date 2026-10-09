import Quillen.Localization.Serre.BasedFiberComparison
import Quillen.Topology.HomotopyFiber.LESTail
import Quillen.Topology.Realization.Connectivity

/-!
# Transport from the actual Serre fiber to the canonical K maps

This is only an adapter for the localization proof. Its explicitly supplied
comparison isomorphism must still be constructed by the geometric theorem.
It is not a localization theorem under the Serre hypotheses alone.
-/
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace Quillen.SerreLocalization
attribute [local instance] Abelian.hasFiniteBiproducts quotientAbelian
variable {C : Type u} [Category.{u} C] [Abelian C]
  (P : ObjectProperty C) [P.IsSerreClass]

/-- The actual fiber connecting map, before transporting to the Serre category. -/
def fiberConnectingHom (n : ℕ) :
    (quotientExactStructure P).K (n + 1) →*
      HomotopyGroup.Pi (n + 1) (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P) :=
  HomotopyFiber.connectingHom (classifyingSpaceMap (quotientNormalizedQ P)).hom
    (quotientExactStructure P).kBasepoint (abelianExactStructure C).kBasepoint
    (quotientExactFunctor P).normalizedQ_map_point n

/-- The transport formula, whose supplied isomorphism remains a proof obligation. -/
def connectingHomOfComparison (n : ℕ)
    (e : (Devissage.subcategoryExactStructure P).K n ≃*
      HomotopyGroup.Pi (n + 1) (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P)) :
    (quotientExactStructure P).K (n + 1) →* (Devissage.subcategoryExactStructure P).K n :=
  e.symm.toMonoidHom.comp (fiberConnectingHom P n)

/-- Exactness at ambient K, once the actual canonical comparison is surjective. -/
theorem inclusion_range_eq_quotient_ker_of_comparison_surjective (n : ℕ)
    (h : Function.Surjective (localizationFiberComparisonHom P n)) :
    (Devissage.KMap P n).range = (quotientKMap P n).ker := by
  have ht := HomotopyFiber.piMap_range_projection_eq_ker
    (classifyingSpaceMap (quotientNormalizedQ P)).hom
    (quotientExactStructure P).kBasepoint (abelianExactStructure C).kBasepoint
    (quotientExactFunctor P).normalizedQ_map_point n
  change (localizationFiberProjectionHom P n).range = (quotientKMap P n).ker at ht
  rw [← ht, ← localizationFiberComparisonHom_projection P n]
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨c, rfl⟩ := h b
    exact ⟨c, rfl⟩

/-- Exactness at quotient K after transport; the map to the fiber is the actual
loop connecting map, and the quotient map remains the canonical K-map. -/
theorem quotient_range_eq_connecting_ker_of_comparison (n : ℕ)
    (e : (Devissage.subcategoryExactStructure P).K n ≃*
      HomotopyGroup.Pi (n + 1) (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P)) :
    (quotientKMap P (n + 1)).range = (connectingHomOfComparison P n e).ker := by
  have ht := HomotopyFiber.range_piMap_eq_ker_connectingHom
    (classifyingSpaceMap (quotientNormalizedQ P)).hom
    (quotientExactStructure P).kBasepoint (abelianExactStructure C).kBasepoint
    (quotientExactFunctor P).normalizedQ_map_point n
  change (quotientKMap P (n + 1)).range = (fiberConnectingHom P n).ker at ht
  rw [ht]
  ext a
  change fiberConnectingHom P n a = 1 ↔ e.symm (fiberConnectingHom P n a) = 1
  exact (map_eq_one_iff e.symm e.symm.injective).symm

/-- Exactness at the Serre category requires the supplied isomorphism to have
exactly the canonical comparison as its forward homomorphism. -/
theorem connecting_range_eq_inclusion_ker_of_comparison (n : ℕ)
    (e : (Devissage.subcategoryExactStructure P).K n ≃*
      HomotopyGroup.Pi (n + 1) (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P))
    (he : e.toMonoidHom = localizationFiberComparisonHom P n) :
    (connectingHomOfComparison P n e).range = (Devissage.KMap P n).ker := by
  have ht := HomotopyFiber.range_connectingHom_eq_ker_projection
    (classifyingSpaceMap (quotientNormalizedQ P)).hom
    (quotientExactStructure P).kBasepoint (abelianExactStructure C).kBasepoint
    (quotientExactFunctor P).normalizedQ_map_point n
  change (fiberConnectingHom P n).range = (localizationFiberProjectionHom P n).ker at ht
  have hp : (localizationFiberProjectionHom P n).comp e.toMonoidHom =
      Devissage.KMap P n := by
    rw [he, localizationFiberComparisonHom_projection]
  have hp' (a : (Devissage.subcategoryExactStructure P).K n) :
      localizationFiberProjectionHom P n (e a) = Devissage.KMap P n a :=
    DFunLike.congr_fun hp a
  ext a
  change (∃ b, e.symm (fiberConnectingHom P n b) = a) ↔ Devissage.KMap P n a = 1
  constructor
  · rintro ⟨b, rfl⟩
    rw [← hp', e.apply_symm_apply]
    have hm : fiberConnectingHom P n b ∈ (fiberConnectingHom P n).range := ⟨b, rfl⟩
    rw [ht] at hm
    exact hm
  · intro ha
    have hm : e a ∈ (localizationFiberProjectionHom P n).ker := (hp' a).trans ha
    rw [← ht] at hm
    obtain ⟨b, hb⟩ := hm
    exact ⟨b, (congrArg e.symm hb).trans (e.symm_apply_apply a)⟩

/-- The connective low-degree tail needs only the actual fiber's connectedness
on π₀; it does not require a separate algebraic K₀ comparison theorem. -/
theorem quotientKZero_surjective_of_fiber_piZero_subsingleton
    [Subsingleton (HomotopyGroup.Pi 0 (NormalizedLocalizationFiber P)
      (normalizedFiberBasepoint P))] : Function.Surjective (quotientKMap P 0) := by
  intro a
  have ht := HomotopyFiber.mem_range_piMap_iff_connectingMap_constant
    (classifyingSpaceMap (quotientNormalizedQ P)).hom
    (quotientExactStructure P).kBasepoint (abelianExactStructure C).kBasepoint
    (quotientExactFunctor P).normalizedQ_map_point 0 a
  exact ht.mpr (@Subsingleton.elim
    (HomotopyGroup.Pi 0 (NormalizedLocalizationFiber P) (normalizedFiberBasepoint P))
    inferInstance _ _)

/-- The K₀ surjectivity needed at the end of localization follows directly
from surjectivity of the genuine fiber comparison on π₀ and connectedness of BQ.
It does not assume a Grothendieck-group identification. -/
theorem quotientKZero_surjective_of_comparison_piZero_surjective
    (h : Function.Surjective (homotopyGroupMap (N := Fin 0)
      (basedLocalizationFiberComparison P) (basedLocalizationFiberComparison_basepoint P))) :
    Function.Surjective (quotientKMap P 0) := by
  let E := Devissage.subcategoryExactStructure P
  letI : PathConnectedSpace E.KSpace := E.kSpace_pathConnected
  have hs : Subsingleton (HomotopyGroup.Pi 0 E.KSpace E.kBasepoint) :=
    (HomotopyGroup.pi0EquivZerothHomotopy (X := E.KSpace) (x := E.kBasepoint)).injective.subsingleton
  letI : Subsingleton (HomotopyGroup.Pi 0 (NormalizedLocalizationFiber P)
      (normalizedFiberBasepoint P)) := ⟨fun a b => by
    obtain ⟨a, rfl⟩ := h a
    obtain ⟨b, rfl⟩ := h b
    exact congrArg (homotopyGroupMap (N := Fin 0) (basedLocalizationFiberComparison P)
      (basedLocalizationFiberComparison_basepoint P)) (hs.elim a b)⟩
  exact quotientKZero_surjective_of_fiber_piZero_subsingleton P

end Quillen.SerreLocalization
