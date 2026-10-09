import Quillen.Scheme.Coherent.Affine.Exact
import Mathlib.CategoryTheory.ObjectProperty.FiniteLimits

/-!
# The affine-local coherent-sheaf property

This object property is defined without noetherianity: quasicoherence together
with finite global sections. On a noetherian affine it is exactly the essential
image of the already constructed actual coherent category. Exactness of that
inclusion proves closure under ambient finite limits and finite colimits.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped ZeroObject
attribute [local instance] Abelian.hasFiniteBiproducts

namespace Quillen.CoherentScheme
variable (R : CommRingCat.{u})

/-- Actual affine quasicoherence and finite generation, with no hidden
noetherianity filter in the predicate. -/
def affineFiniteSheaf : ObjectProperty (Spec R).Modules := fun M =>
  M.IsQuasicoherent ∧ Module.Finite R (moduleSpecΓFunctor.obj M)

instance affineFiniteSheaf_isoClosed : (affineFiniteSheaf R).IsClosedUnderIsomorphisms where
  of_iso e h := by
    have : Module.Finite R (moduleSpecΓFunctor.obj _) := h.2
    exact ⟨(SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e h.1,
      Module.Finite.equiv (moduleSpecΓFunctor.mapIso e).toLinearEquiv⟩

variable [IsNoetherianRing R]

/-- This is the essential image of actual coherent sheaves, not a substitute
category with merely postulated coherent behavior. -/
theorem affineFiniteSheaf_eq_essImage :
    affineFiniteSheaf R = (affineCoherentToSheaves R).essImage := by
  funext M
  apply propext
  constructor
  · intro h
    exact ⟨⟨⟨M, h.1⟩, h.2⟩, ⟨Iso.refl M⟩⟩
  · rintro ⟨N, ⟨e⟩⟩
    exact (affineFiniteSheaf R).prop_of_iso e ⟨N.obj.property, N.property⟩

instance affineFiniteSheaf_containsZero : (affineFiniteSheaf R).ContainsZero where
  exists_zero := ⟨(affineCoherentToSheaves R).obj 0,
    (affineCoherentToSheaves R).map_isZero (isZero_zero _), by
      rw [affineFiniteSheaf_eq_essImage]
      exact ⟨0, ⟨Iso.refl _⟩⟩⟩

instance affineFiniteSheaf_finiteLimits : (affineFiniteSheaf R).IsClosedUnderFiniteLimits where
  isClosedUnderLimitsOfShape J _ _ := by
    rw [affineFiniteSheaf_eq_essImage]
    infer_instance

instance affineFiniteSheaf_finiteColimits : (affineFiniteSheaf R).IsClosedUnderFiniteColimits where
  isClosedUnderColimitsOfShape J _ _ := by
    rw [affineFiniteSheaf_eq_essImage]
    infer_instance

end Quillen.CoherentScheme
