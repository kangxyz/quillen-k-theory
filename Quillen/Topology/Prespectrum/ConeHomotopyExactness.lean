/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.CoherentHomotopyCongruence
public import Quillen.Topology.Prespectrum.HomotopyTransport

/-!
# Mapping out of the actual cone in the coherent homotopy category

The original cone inclusion is exact for contravariant maps in the coherent homotopy category:
a map out of its target extends over the actual cone exactly when its restriction along the
original arrow is coherently nullhomotopic. The result applies to every morphism of the existing
quotient category, not only a supplied nullhomotopy. The universal property also remembers the
whole nullhomotopy before passage to the quotient. Stable localization is a separate step, and
no stable excision or stable-group exactness follows from this result alone.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe u

namespace Quillen.LoopPrespectrum

variable {E F G : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- Restrict a map from the actual cone to its entire original cylinder. -/
def mappingConeRestrictionHomotopy (h : mappingCone f ⟶ G) :
    Homotopy (f ≫ mappingConeInclusion f ≫ h) (zeroHom E G) :=
  ((mappingConeHomotopy f).postcomp h).cast (Category.assoc _ _ _) (by
    apply Hom.ext
    funext n
    ext x
    exact h.map_point n)

/-- Every point of the original cylinder remains the restricted nullhomotopy. -/
@[simp]
theorem mappingConeRestrictionHomotopy_apply (h : mappingCone f ⟶ G)
    (n : ℕ) (s : unitInterval) (x : E.space n) :
    (mappingConeRestrictionHomotopy f h).level n (s, x) =
      h.map n (ReducedMappingCone.cylinder (E.point n) (F.point n) (f.map n) (s, x)) := rfl

/-- Descending a cone map's original restriction and entire cylinder recovers that map. -/
@[simp]
theorem mappingConeDesc_restriction (h : mappingCone f ⟶ G) :
    mappingConeDesc f (mappingConeInclusion f ≫ h) (mappingConeRestrictionHomotopy f h) = h := by
  apply mappingCone_hom_ext
  · exact mappingConeInclusion_desc _ _ _
  · intro n s x
    rfl

/-- Strict maps out of the cone are equivalent to original target maps equipped with their
whole coherent based nullhomotopies. -/
def mappingConeHomEquiv :
    (mappingCone f ⟶ G) ≃ Σ g : F ⟶ G, Homotopy (f ≫ g) (zeroHom E G) where
  toFun h := ⟨mappingConeInclusion f ≫ h, mappingConeRestrictionHomotopy f h⟩
  invFun p := mappingConeDesc f p.1 p.2
  left_inv := mappingConeDesc_restriction f
  right_inv p := by
    rcases p with ⟨g, H⟩
    apply Sigma.ext (mappingConeInclusion_desc f g H)
    apply heq_of_eq
    apply Homotopy.ext
    funext n
    ext z
    rfl

/-- The original target map extends strictly over the actual cone precisely when its original
composite has a whole coherent nullhomotopy. -/
theorem mappingCone_exists_extension_iff (g : F ⟶ G) :
    (∃ h : mappingCone f ⟶ G, mappingConeInclusion f ≫ h = g) ↔
      Nonempty (Homotopy (f ≫ g) (zeroHom E G)) := by
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨mappingConeRestrictionHomotopy f h⟩
  · rintro ⟨H⟩
    exact ⟨mappingConeDesc f g H, mappingConeInclusion_desc _ _ _⟩

/-- Every arrow in the actual coherent homotopy quotient satisfies the mapping-out exactness
property of the original cone inclusion. No stable-localization assertion is used. -/
theorem coherentMappingCone_exact
    (g : coherentHomotopyQuotient.obj F ⟶ coherentHomotopyQuotient.obj G) :
    coherentHomotopyQuotient.map f ≫ g = coherentHomotopyQuotient.map (zeroHom E G) ↔
      ∃ h : coherentHomotopyQuotient.obj (mappingCone f) ⟶ coherentHomotopyQuotient.obj G,
        coherentHomotopyQuotient.map (mappingConeInclusion f) ≫ h = g := by
  obtain ⟨g, rfl⟩ := coherentHomotopyQuotient.map_surjective g
  constructor
  · intro hg
    rw [← Functor.map_comp, coherentHomotopyQuotient_map_eq_iff] at hg
    obtain ⟨h, hh⟩ := (mappingCone_exists_extension_iff f g).mpr hg
    exact ⟨coherentHomotopyQuotient.map h, by rw [← Functor.map_comp, hh]⟩
  · rintro ⟨h, hh⟩
    obtain ⟨h, rfl⟩ := coherentHomotopyQuotient.map_surjective h
    rw [← hh, ← Functor.map_comp, ← Functor.map_comp]
    apply coherentHomotopyQuotient_map_eq
    exact (mappingConeRestrictionHomotopy f h).cast (Category.assoc _ _ _).symm rfl

end Quillen.LoopPrespectrum
