/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.ClassifyingSpace.ZeroSkeleton

/-! Original vertices in the actual nerve skeleton retain their original object
coordinate, before and after the canonical inclusion into the classifying space. -/
@[expose] public section

noncomputable section
open CategoryTheory
open scoped Simplicial Topology
universe u v
namespace Quillen.Tests
variable {C : Type u} [Category.{v} C]

/-- Distinct original objects give distinct components in the actual vertex skeleton. -/
theorem zeroSkeleton_original_vertex_classes_eq_iff (c₀ a b : C) :
    zeroPointClass (nerveZeroSkeletonPoint c₀) (nerveZeroSkeletonPoint a) =
      zeroPointClass (nerveZeroSkeletonPoint c₀) (nerveZeroSkeletonPoint b) ↔ a = b :=
  ⟨fun h ↦ (nerveZeroSkeletonPoint_zeroPointClass_bijective c₀).injective h,
    by rintro rfl; rfl⟩

/-- Every original zero class has a unique original object representative. -/
theorem zeroSkeleton_unique_original_object (c₀ : C)
    (x : HomotopyGroup.Pi 0 |((nerve C).skeleton 1 : SSet.{max u v})|
      (nerveZeroSkeletonPoint c₀)) :
    ∃! c : C, zeroPointClass (nerveZeroSkeletonPoint c₀) (nerveZeroSkeletonPoint c) = x := by
  obtain ⟨c, hc⟩ := (nerveZeroSkeletonPoint_zeroPointClass_bijective c₀).surjective x
  exact ⟨c, hc, fun d hd ↦
    (nerveZeroSkeletonPoint_zeroPointClass_bijective c₀).injective (hd.trans hc.symm)⟩

/-- The canonical discrete-object coordinates include as the actual original vertex. -/
theorem zeroSkeleton_discrete_inverse_inclusion (c : C) :
    SSet.toTop.map ((nerve C).skeleton 1).ι
      ((nerveZeroSkeletonRealizationIso (C := C)).inv (ULift.up c)) =
        classifyingSpacePoint c := by
  rw [nerveZeroSkeletonRealizationIso_inv_object, nerveZeroSkeletonPoint_inclusion]

end Quillen.Tests
