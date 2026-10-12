/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.CategoryTheory.Monoidal.TranslationTelescopeShift
public import Quillen.Topology.ClassifyingSpace.TelescopeShift
public import Quillen.Topology.ClassifyingSpace.UniverseHomotopy

/-!
# Right-stabilization equivalence in the original monoidal telescope model

The forward map is proved equal to the original right-stabilization functor's
classifying map. Its component bijectivity therefore applies to that map.
-/

@[expose] public section
noncomputable section
open CategoryTheory MonoidalCategory
universe u v
namespace Quillen.TranslationTelescope
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (e : C)

/-- Transport the genuine stabilization equivalence through the explicit model equivalence. -/
def rightStabilizationClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Model e)) (ClassifyingSpace (Model e)) :=
  ((equivalenceClassifyingHomotopyEquivUniversal (modelEquivalence e)).trans
    (EndofunctorTelescope.stabilizationClassifyingHomotopyEquiv (tensorRight e))).trans
      (equivalenceClassifyingHomotopyEquivUniversal (modelEquivalence e)).symm

/-- The transported forward map is exactly the original right stabilization. -/
theorem rightStabilizationClassifyingHomotopyEquiv_toFun :
    (rightStabilizationClassifyingHomotopyEquiv e).toFun =
      (classifyingSpaceMap (rightStabilization e)).hom := by
  change (classifyingSpaceMapUniversal (modelEquivalence e).inverse).comp
    ((classifyingSpaceMap (EndofunctorTelescope.stabilization (tensorRight e))).hom.comp
      (classifyingSpaceMapUniversal (modelEquivalence e).functor)) = _
  rw [← classifyingSpaceMapUniversal_eq,
    ← classifyingSpaceMapUniversal_comp, ← classifyingSpaceMapUniversal_comp]
  exact classifyingSpaceMapUniversal_eq _

/-- The inverse is the actual index-shift map in this same model. -/
theorem rightStabilizationClassifyingHomotopyEquiv_invFun :
    (rightStabilizationClassifyingHomotopyEquiv e).invFun =
      (classifyingSpaceMap (indexShift e)).hom := by
  change (classifyingSpaceMapUniversal (modelEquivalence e).inverse).comp
    ((classifyingSpaceMap (EndofunctorTelescope.shift (tensorRight e))).hom.comp
      (classifyingSpaceMapUniversal (modelEquivalence e).functor)) = _
  rw [← classifyingSpaceMapUniversal_eq,
    ← classifyingSpaceMapUniversal_comp, ← classifyingSpaceMapUniversal_comp]
  exact classifyingSpaceMapUniversal_eq _

/-- Right stabilization reflects the actual component relation in the precompletion model. -/
theorem rightStabilization_joined_iff (x y : ClassifyingSpace (Model e)) :
    Joined (classifyingSpaceMap (rightStabilization e) x)
      (classifyingSpaceMap (rightStabilization e) y) ↔ Joined x y := by
  change Joined ((classifyingSpaceMap (rightStabilization e)).hom x)
    ((classifyingSpaceMap (rightStabilization e)).hom y) ↔ Joined x y
  rw [← rightStabilizationClassifyingHomotopyEquiv_toFun e]
  let h := rightStabilizationClassifyingHomotopyEquiv e
  obtain ⟨H⟩ := h.left_inv
  constructor
  · intro hxy
    exact (show Joined x (h.invFun (h.toFun x)) from ⟨(H.evalAt x).symm⟩).trans
      ((hxy.map h.invFun.continuous).trans ⟨H.evalAt y⟩)
  · exact fun hxy ↦ hxy.map h.toFun.continuous

/-- Every component is reached by the actual right-stabilization map. -/
theorem exists_joined_rightStabilization (y : ClassifyingSpace (Model e)) :
    ∃ x, Joined (classifyingSpaceMap (rightStabilization e) x) y := by
  change ∃ x, Joined ((classifyingSpaceMap (rightStabilization e)).hom x) y
  rw [← rightStabilizationClassifyingHomotopyEquiv_toFun e]
  obtain ⟨H⟩ := (rightStabilizationClassifyingHomotopyEquiv e).right_inv
  exact ⟨(rightStabilizationClassifyingHomotopyEquiv e).invFun y, ⟨H.evalAt y⟩⟩

end Quillen.TranslationTelescope
