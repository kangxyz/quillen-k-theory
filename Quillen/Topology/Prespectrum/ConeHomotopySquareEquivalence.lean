/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.ConeArrowHomotopy
public import Quillen.Topology.Prespectrum.ConeHomotopySquare
public import Quillen.Topology.Prespectrum.MappingConeWeakEquivalence

/-!
# Weak and stable comparison of the original whole-track cone map

The existing mappingConeSquareMap factors literally into a strict target-change cone map, the
actual arrow-change map carrying the supplied whole homotopy, and a strict source-change cone map.
The middle map has the constructed reverse-track homotopy inverse. Complete weak side maps and
HEP at the four actual points therefore imply weakness of the unchanged cone-square map. Positive
levels suffice for its stable equivalence, and connected Omega corners supply those side tests.
-/
@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum

variable {E F E' F' : LoopPrespectrum.{u}}
  (f : E ⟶ F) (g : E' ⟶ F') (a : E ⟶ E') (b : F ⟶ F')
  (H : Homotopy (f ≫ b) (a ≫ g))

/-- The actual cone-square map factors on both its original target and its entire original
cylinder, with the supplied whole square track retained in the middle factor. -/
theorem mappingConeSquareMap_factor :
    mappingConeSquareMap f g a b H =
      mappingConeMap (Arrow.homMk (f := Arrow.mk f) (g := Arrow.mk (f ≫ b))
        (𝟙 E) b (by simp)) ≫
      mappingConeHomotopyMap H ≫
      mappingConeMap (Arrow.homMk (f := Arrow.mk (a ≫ g)) (g := Arrow.mk g)
        a (𝟙 F') (by simp)) := by
  apply mappingCone_hom_ext
  · apply Hom.ext
    funext n
    ext y
    rfl
  · intro n s x
    change (((H.postcomp (mappingConeInclusion g)).levelHomotopy n).trans
        ((Homotopy.precomp a (mappingConeHomotopy g)).levelHomotopy n)) (s, x) =
      (mappingConeMap (Arrow.homMk (f := Arrow.mk (a ≫ g)) (g := Arrow.mk g)
        a (𝟙 F') (by simp))).map n
          ((((H.postcomp (mappingConeInclusion (a ≫ g))).levelHomotopy n).trans
            ((mappingConeHomotopy (a ≫ g)).levelHomotopy n)) (s, x))
    simp only [ContinuousMap.HomotopyRel.trans_apply]
    split <;> rfl

variable
  (hE : ∀ n, Quillen.homotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point (n + 1)))))
  (hF : ∀ n, Quillen.homotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (F.point (n + 1)))))
  (hE' : ∀ n, Quillen.homotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E'.point (n + 1)))))
  (hF' : ∀ n, Quillen.homotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (F'.point (n + 1)))))
include hE hF hE' hF'

/-- Complete weak side maps give complete weakness of the unchanged supplied-track cone map at
every original positive level, with only actual point HEP added. -/
theorem mappingConeSquareMap_positiveLevel_isWeakHomotopyEquivalence
    (ha : ∀ n, IsWeakHomotopyEquivalence (a.map (n + 1)))
    (hb : ∀ n, IsWeakHomotopyEquivalence (b.map (n + 1))) (n : ℕ) :
    IsWeakHomotopyEquivalence ((mappingConeSquareMap f g a b H).map (n + 1)) := by
  let sq₁ : Arrow.mk f ⟶ Arrow.mk (f ≫ b) := Arrow.homMk (𝟙 E) b (by simp)
  let sq₂ : Arrow.mk (a ≫ g) ⟶ Arrow.mk g := Arrow.homMk a (𝟙 F') (by simp)
  have h₁ := mappingConeMap_positiveLevel_isWeakHomotopyEquivalence sq₁ hE hF hE hF'
    (fun k ↦ isWeakHomotopyEquivalence_id (E.space (k + 1))) hb n
  have h₂ := mappingConeMap_positiveLevel_isWeakHomotopyEquivalence sq₂ hE hF' hE' hF'
    ha (fun k ↦ isWeakHomotopyEquivalence_id (F'.space (k + 1))) n
  rw [mappingConeSquareMap_factor]
  exact h₂.comp ((mappingConeHomotopyMap_level_isWeakHomotopyEquivalence H (n + 1)).comp h₁)

/-- The original whole-track cone map preserves stable equivalence under positive-level weak
side maps and actual positive-level point HEP, without an Omega premise on its cones. -/
theorem mappingConeSquareMap_isStableEquivalence_of_positiveLevel
    (ha : ∀ n, IsWeakHomotopyEquivalence (a.map (n + 1)))
    (hb : ∀ n, IsWeakHomotopyEquivalence (b.map (n + 1))) :
    IsStableEquivalence (mappingConeSquareMap f g a b H) :=
  isStableEquivalence_of_positiveLevel _
    (mappingConeSquareMap_positiveLevel_isWeakHomotopyEquivalence
      f g a b H hE hF hE' hF' ha hb)

/-- Stable side equivalences on actual connected Omega corners give a stable equivalence on the
existing whole-track cone map. The four original point HEP inputs remain explicit. -/
theorem mappingConeSquareMap_isStableEquivalence_of_omega
    (hOmegaE : E.IsOmega) (hOmegaF : F.IsOmega)
    (hOmegaE' : E'.IsOmega) (hOmegaF' : F'.IsOmega)
    (hconnE : ∀ n, PathConnectedSpace (E.space (n + 1)))
    (hconnF : ∀ n, PathConnectedSpace (F.space (n + 1)))
    (hconnE' : ∀ n, PathConnectedSpace (E'.space (n + 1)))
    (hconnF' : ∀ n, PathConnectedSpace (F'.space (n + 1)))
    (ha : IsStableEquivalence a) (hb : IsStableEquivalence b) :
    IsStableEquivalence (mappingConeSquareMap f g a b H) :=
  mappingConeSquareMap_isStableEquivalence_of_positiveLevel f g a b H hE hF hE' hF'
    (positiveLevel_isWeakHomotopyEquivalence_of_isStableEquivalence
      hOmegaE hOmegaE' a ha hconnE hconnE')
    (positiveLevel_isWeakHomotopyEquivalence_of_isStableEquivalence
      hOmegaF hOmegaF' b hb hconnF hconnF')

end Quillen.LoopPrespectrum
