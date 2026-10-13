/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyCofiber.ReducedMappingConeWeakEquivalence
public import Quillen.Topology.Prespectrum.MappingCone
public import Quillen.Topology.Prespectrum.PositiveLevelEquivalence
public import Quillen.Topology.Prespectrum.StableOmegaDetection

/-!
# Stable comparison of actual reduced mapping cones

Strict arrow squares with complete weak side maps at positive levels induce stable equivalences
of the original cone prespectra when the four positive-level chosen points have HEP. For connected
Omega-prespectra, the side hypothesis follows from original stable equivalence. Both versions keep
the existing mappingConeMap, without assuming cofiber exactness or any weak-map inverse.
-/
@[expose] public section
noncomputable section

open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum

variable {A B : Arrow LoopPrespectrum.{u}} (sq : A ⟶ B)
  (hAL : ∀ n, Quillen.homotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A.left.point (n + 1)))))
  (hAR : ∀ n, Quillen.homotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (A.right.point (n + 1)))))
  (hBL : ∀ n, Quillen.homotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B.left.point (n + 1)))))
  (hBR : ∀ n, Quillen.homotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (B.right.point (n + 1)))))
include hAL hAR hBL hBR

/-- The original positive-level cone map is a complete weak equivalence under actual point HEP. -/
theorem mappingConeMap_positiveLevel_isWeakHomotopyEquivalence
    (hl : ∀ n, IsWeakHomotopyEquivalence (sq.left.map (n + 1)))
    (hr : ∀ n, IsWeakHomotopyEquivalence (sq.right.map (n + 1))) (n : ℕ) :
    IsWeakHomotopyEquivalence ((mappingConeMap sq).map (n + 1)) :=
  ReducedMappingCone.map_isWeakHomotopyEquivalence
    (A.left.point (n + 1)) (A.right.point (n + 1)) (A.hom.map (n + 1)) (A.hom.map_point (n + 1))
    (B.left.point (n + 1)) (B.right.point (n + 1)) (B.hom.map (n + 1)) (B.hom.map_point (n + 1))
    (sq.left.map (n + 1)) (sq.right.map (n + 1))
    (sq.left.map_point (n + 1)) (sq.right.map_point (n + 1))
    (fun x ↦ congrArg (fun h ↦ h.map (n + 1) x) sq.w.symm)
    (hAL n) (hAR n) (hBL n) (hBR n) (hl n) (hr n)

/-- Positive-level weak side maps induce a stable equivalence on the unchanged mapping-cone map. -/
theorem mappingConeMap_isStableEquivalence_of_positiveLevel
    (hl : ∀ n, IsWeakHomotopyEquivalence (sq.left.map (n + 1)))
    (hr : ∀ n, IsWeakHomotopyEquivalence (sq.right.map (n + 1))) :
    IsStableEquivalence (mappingConeMap sq) :=
  isStableEquivalence_of_positiveLevel _
    (mappingConeMap_positiveLevel_isWeakHomotopyEquivalence sq hAL hAR hBL hBR hl hr)

/-- Stable equivalences of the actual connected Omega corners suffice for the original cone map,
with well-basedness supplied at the four actual positive-level points. -/
theorem mappingConeMap_isStableEquivalence_of_omega
    (hOmegaAL : A.left.IsOmega) (hOmegaAR : A.right.IsOmega)
    (hOmegaBL : B.left.IsOmega) (hOmegaBR : B.right.IsOmega)
    (hconnAL : ∀ n, PathConnectedSpace (A.left.space (n + 1)))
    (hconnAR : ∀ n, PathConnectedSpace (A.right.space (n + 1)))
    (hconnBL : ∀ n, PathConnectedSpace (B.left.space (n + 1)))
    (hconnBR : ∀ n, PathConnectedSpace (B.right.space (n + 1)))
    (hl : IsStableEquivalence sq.left) (hr : IsStableEquivalence sq.right) :
    IsStableEquivalence (mappingConeMap sq) :=
  mappingConeMap_isStableEquivalence_of_positiveLevel sq hAL hAR hBL hBR
    (positiveLevel_isWeakHomotopyEquivalence_of_isStableEquivalence
      hOmegaAL hOmegaBL sq.left hl hconnAL hconnBL)
    (positiveLevel_isWeakHomotopyEquivalence_of_isStableEquivalence
      hOmegaAR hOmegaBR sq.right hr hconnAR hconnBR)

end Quillen.LoopPrespectrum

namespace Quillen.LoopPrespectrum

/-- The actual reduced mapping cone preserves HEP of its original positive-level points. -/
theorem mappingCone_positivePoint_homotopyExtensionProperty
    {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
    (hE : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point (n + 1)))))
    (hF : ∀ n, Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (F.point (n + 1))))) (n : ℕ) :
    Quillen.homotopyExtensionProperty (TopCat.ofHom
      (ContinuousMap.const PUnit.{u + 1} ((mappingCone f).point (n + 1)))) :=
  ReducedMappingCone.point_homotopyExtensionProperty
    (E.point (n + 1)) (F.point (n + 1)) (f.map (n + 1)) (f.map_point (n + 1)) (hE n) (hF n)

end Quillen.LoopPrespectrum
