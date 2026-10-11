/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.ClassifyingSpace.CharacteristicPoints

/-! Actual nerve cells are loops precisely when their original endpoint objects
agree, as an equality of the original realized characteristic endpoint points. -/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped Simplicial Topology
universe u v
namespace Quillen.Tests
variable {C : Type u} [Category.{v} C]

/-- A genuine characteristic one-cell has equal endpoint points exactly when its
original source and target objects agree. -/
theorem actualNerveOneCell_closed_iff
    (a : SSet.relativeCellComplexOfMono.Cell ((⊥ : (nerve C).Subcomplex).ι) 1) :
    SSet.toTop.map (SSet.skeletonOfMono ((⊥ : (nerve C).Subcomplex).ι) 2).ι
      (realizedSkeletalCharacteristic ((⊥ : (nerve C).Subcomplex).ι) 1
        (a, SimplexCategory.toTopHomeo ⦋1⦌ (realizationInterval.{max u v} 0))) =
    SSet.toTop.map (SSet.skeletonOfMono ((⊥ : (nerve C).Subcomplex).ι) 2).ι
      (realizedSkeletalCharacteristic ((⊥ : (nerve C).Subcomplex).ι) 1
        (a, SimplexCategory.toTopHomeo ⦋1⦌ (realizationInterval.{max u v} 1))) ↔
      a.simplex.obj 0 = a.simplex.obj 1 := by
  rw [realizedNerveOneCell_original_source, realizedNerveOneCell_original_target]
  exact ⟨fun h ↦ classifyingSpacePoint_injective h, congrArg classifyingSpacePoint⟩

end Quillen.Tests
