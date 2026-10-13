/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.ConeContraction
public import Quillen.Topology.Prespectrum.ConeFiberComparison
public import Quillen.Topology.Prespectrum.FiberWeakEquivalence
public import Quillen.Topology.Prespectrum.MappingConeWeakEquivalence
public import Quillen.Topology.HomotopyFiber.ContractibleBase

/-!
# The canonical cone-to-fiber comparison for positive-level weak arrows

The original identity cone is genuinely contracted. Its actual fiber projection is therefore a
complete weak equivalence, and so is the same canonical source-to-fiber comparison. For an original
arrow that is a complete weak equivalence at positive levels, strict-square naturality and the
proved cone and fiber weak-invariance theorems give complete weak equivalences of its canonical
comparison at those levels. The source and target chosen points must have HEP there.

This proves the corresponding stable equivalence and vanishing of the actual cone's stable groups
in every integer degree. It does not apply to arbitrary stable equivalences, and it is not general
stable excision for arbitrary arrows.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe u

namespace Quillen.LoopPrespectrum

/-- For an identity arrow, the same canonical comparison is a complete weak equivalence at every
level, using the actual contraction of its cone and its original fiber projection. -/
theorem mappingConeFiberComparison_id_level_isWeakHomotopyEquivalence
    (E : LoopPrespectrum.{u}) (n : ℕ) :
    IsWeakHomotopyEquivalence ((mappingConeFiberComparison (𝟙 E)).map n) := by
  have hp : IsWeakHomotopyEquivalence
      ((homotopyFiberProjection (mappingConeInclusion (𝟙 E))).map n) :=
    isWeakHomotopyEquivalence_of_homotopyEquiv
      (HomotopyFiber.projectionEquivOfContraction ((mappingConeInclusion (𝟙 E)).map n)
        ((mappingCone (𝟙 E)).point n) ((mappingConeIdContraction E).levelHomotopy n).toHomotopy)
  have hcomp : IsWeakHomotopyEquivalence
      (((homotopyFiberProjection (mappingConeInclusion (𝟙 E))).map n).comp
        ((mappingConeFiberComparison (𝟙 E)).map n)) :=
    isWeakHomotopyEquivalence_id (E.space n)
  exact hcomp.of_comp_right hp

variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)

/-- The original arrow and the identity of its target form their strict comparison square. -/
def mappingConeIdentitySquare : Arrow.mk f ⟶ Arrow.mk (𝟙 F) :=
  Arrow.homMk f (𝟙 F) (by simp)

variable
  (hE : ∀ n, Quillen.homotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point (n + 1)))))
  (hF : ∀ n, Quillen.homotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (F.point (n + 1)))))
  (hf : ∀ n, IsWeakHomotopyEquivalence (f.map (n + 1)))

include hE hF hf

/-- Complete positive-level weak arrows have genuinely vanishing actual cone stable groups,
by comparison with the constructed identity-cone contraction. -/
theorem mappingCone_stableHomotopyGroup_subsingleton_of_positiveLevel (d : ℤ) :
    Subsingleton (stableHomotopyGroup (mappingCone f) d) := by
  have hw := mappingConeMap_isStableEquivalence_of_positiveLevel (mappingConeIdentitySquare f)
    hE hF hF hF hf (fun n ↦ isWeakHomotopyEquivalence_id (F.space (n + 1)))
  have hinj := ((ConcreteCategory.isIso_iff_bijective _).mp (hw d)).injective
  exact ⟨fun a b ↦ hinj ((mappingCone_id_stableHomotopyGroup_subsingleton F d).elim _ _)⟩

/-- Under actual point HEP and complete positive-level weakness of the original arrow, its same
canonical cone-to-fiber comparison is itself a complete positive-level weak equivalence. -/
theorem mappingConeFiberComparison_positiveLevel_isWeakHomotopyEquivalence (n : ℕ) :
    IsWeakHomotopyEquivalence ((mappingConeFiberComparison f).map (n + 1)) := by
  let sq := mappingConeIdentitySquare f
  have hc := mappingConeMap_positiveLevel_isWeakHomotopyEquivalence sq
    hE hF hF hF hf (fun k ↦ isWeakHomotopyEquivalence_id (F.space (k + 1))) n
  have hp := homotopyFiberMap_level_isWeakHomotopyEquivalence
    (mappingConeInclusionSquare sq) (n + 1)
    (isWeakHomotopyEquivalence_id (F.space (n + 1))) hc
  have hcomp : IsWeakHomotopyEquivalence
      (((homotopyFiberMap (mappingConeInclusionSquare sq)).map (n + 1)).comp
        ((mappingConeFiberComparison f).map (n + 1))) := by
    have he := congrArg (fun h ↦ h.map (n + 1)) (mappingConeFiberComparison_naturality sq)
    change ((mappingConeFiberComparison (𝟙 F)).map (n + 1)).comp (f.map (n + 1)) =
      ((homotopyFiberMap (mappingConeInclusionSquare sq)).map (n + 1)).comp
        ((mappingConeFiberComparison f).map (n + 1)) at he
    rw [← he]
    exact (mappingConeFiberComparison_id_level_isWeakHomotopyEquivalence F (n + 1)).comp (hf n)
  exact hcomp.of_comp_right hp

/-- The original comparison is a stable equivalence in the positive-level complete weak case.
No assertion for arbitrary stable-equivalent or arbitrary original arrows is used. -/
theorem mappingConeFiberComparison_isStableEquivalence_of_positiveLevel :
    IsStableEquivalence (mappingConeFiberComparison f) :=
  isStableEquivalence_of_positiveLevel _
    (mappingConeFiberComparison_positiveLevel_isWeakHomotopyEquivalence f hE hF hf)

end Quillen.LoopPrespectrum
