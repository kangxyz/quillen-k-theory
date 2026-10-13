/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.CategoryTheory.Grothendieck.TelescopeShift
public import Quillen.Topology.ClassifyingSpace.Equivalence

/-!
# The original right-stabilization map is a telescope homotopy equivalence

The homotopy inverse is the actual index shift. The unit homotopies retain the
original Grothendieck stabilization arrows, and the component criteria refer
to the original stabilization map rather than an unspecified equivalence.
-/

@[expose] public section
noncomputable section
open CategoryTheory
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace Quillen.EndofunctorTelescope
variable {C : Type u} [Category.{v} C] (T : C ⥤ C)

/-- The original stabilization arrows realize to the first inverse homotopy. -/
def stabilizationShiftClassifyingHomotopy :
    (ContinuousMap.id (ClassifyingSpace (Model T))).Homotopy
      ((classifyingSpaceMap (shift T)).hom.comp
        (classifyingSpaceMap (stabilization T)).hom) := by
  simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
    TopCat.hom_comp] using
    classifyingSpaceNaturalTransformationHomotopy (stabilizationShiftUnit T)

/-- The other inverse homotopy uses the same canonical stabilization arrows. -/
def shiftStabilizationClassifyingHomotopy :
    (ContinuousMap.id (ClassifyingSpace (Model T))).Homotopy
      ((classifyingSpaceMap (stabilization T)).hom.comp
        (classifyingSpaceMap (shift T)).hom) := by
  simpa only [classifyingSpaceMap_id, classifyingSpaceMap_comp, TopCat.hom_id,
    TopCat.hom_comp] using
    classifyingSpaceNaturalTransformationHomotopy (shiftStabilizationUnit T)

/-- The genuine equivalence whose forward map is the original stagewise stabilization. -/
def stabilizationClassifyingHomotopyEquiv :
    ContinuousMap.HomotopyEquiv (ClassifyingSpace (Model T))
      (ClassifyingSpace (Model T)) where
  toFun := (classifyingSpaceMap (stabilization T)).hom
  invFun := (classifyingSpaceMap (shift T)).hom
  left_inv := ⟨(stabilizationShiftClassifyingHomotopy T).symm⟩
  right_inv := ⟨(shiftStabilizationClassifyingHomotopy T).symm⟩

/-- Right stabilization reflects and preserves the actual path-component relation. -/
theorem stabilization_joined_iff (x y : ClassifyingSpace (Model T)) :
    Joined (classifyingSpaceMap (stabilization T) x)
      (classifyingSpaceMap (stabilization T) y) ↔ Joined x y := by
  constructor
  · intro h
    exact (show Joined x ((classifyingSpaceMap (shift T))
      ((classifyingSpaceMap (stabilization T)) x)) from
      ⟨(stabilizationShiftClassifyingHomotopy T).evalAt x⟩).trans
      ((h.map (classifyingSpaceMap (shift T)).hom.continuous).trans
        ⟨((stabilizationShiftClassifyingHomotopy T).evalAt y).symm⟩)
  · exact fun h ↦ h.map (classifyingSpaceMap (stabilization T)).hom.continuous

/-- Every component is hit by the original stabilization map. -/
theorem exists_joined_stabilization (y : ClassifyingSpace (Model T)) :
    ∃ x, Joined (classifyingSpaceMap (stabilization T) x) y :=
  ⟨classifyingSpaceMap (shift T) y,
    ⟨((shiftStabilizationClassifyingHomotopy T).evalAt y).symm⟩⟩

/-- The actual stage map remains unchanged under passage to classifying spaces. -/
theorem inclusion_stabilization_classifying (n : ℕ) :
    classifyingSpaceMap (Grothendieck.ι (diagram T) n) ≫
        classifyingSpaceMap (stabilization T) =
      classifyingSpaceMap T ≫ classifyingSpaceMap (Grothendieck.ι (diagram T) n) := by
  rw [← classifyingSpaceMap_comp, inclusion_stabilization]
  exact classifyingSpaceMap_comp T (Grothendieck.ι (diagram T) n)

end Quillen.EndofunctorTelescope
