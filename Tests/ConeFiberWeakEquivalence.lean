/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.ConeFiberWeakEquivalence

/-!
# Original comparison consumers for complete weak arrows

The identity-cone contraction keeps its two independent geometric parameters. The canonical
comparison covers every actual positive-level fiber component and lifts every original stable
fiber class with its projected original arrow unchanged. The identity case includes level zero
and requires no point HEP.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Quillen Quillen.LoopPrespectrum
open scoped Topology unitInterval

universe u

namespace Quillen.Tests.ConeFiberWeakEquivalence

/-- The identity contraction keeps the moving cone height independent of structure time. -/
theorem identity_contraction_original_structure (E : LoopPrespectrum.{u})
    (n : ℕ) (r s t : unitInterval) (x : E.space n) :
    (mappingConeIdContraction E).level (n + 1)
      (r, ReducedMappingCone.cylinder (E.point (n + 1)) (E.point (n + 1))
        ((𝟙 E : E ⟶ E).map (n + 1)) (s, E.structureMap n x t)) =
      (mappingCone (𝟙 E)).structureMap n
        (ReducedMappingCone.cylinder (E.point n) (E.point n) ((𝟙 E : E ⟶ E).map n)
          (unitInterval.symm (unitInterval.symm r * unitInterval.symm s), x)) t :=
  (mappingConeIdContraction E).comm n r
    (ReducedMappingCone.cylinder (E.point n) (E.point n) ((𝟙 E : E ⟶ E).map n) (s, x)) t

/-- Even at level zero, the original identity comparison covers every actual fiber component,
without any point HEP or separation hypothesis. -/
theorem identity_comparison_covers_level_zero (E : LoopPrespectrum.{u})
    (z : (homotopyFiber (mappingConeInclusion (𝟙 E))).space 0) :
    ∃ x : E.space 0, Joined ((mappingConeFiberComparison (𝟙 E)).map 0 x) z :=
  (mappingConeFiberComparison_id_level_isWeakHomotopyEquivalence E 0).component_surjective z

variable {E F : LoopPrespectrum.{u}} (f : E ⟶ F)
  (hE : ∀ n, Quillen.homotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (E.point (n + 1)))))
  (hF : ∀ n, Quillen.homotopyExtensionProperty
    (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (F.point (n + 1)))))
  (hf : ∀ n, IsWeakHomotopyEquivalence (f.map (n + 1)))

include hE hF hf

/-- The result includes the path components of actual fiber points, with the original cylinder
as the comparison path. -/
theorem original_fiber_components_covered (n : ℕ)
    (z : (homotopyFiber (mappingConeInclusion f)).space (n + 1)) :
    ∃ x : E.space (n + 1), Joined ((mappingConeFiberComparison f).map (n + 1) x) z := by
  have h := mappingConeFiberComparison_positiveLevel_isWeakHomotopyEquivalence f hE hF hf n
  exact h.component_surjective z

/-- A class in the actual fiber lifts through the same canonical comparison in every integer
degree, and its projection is the image under the unchanged original arrow. -/
theorem original_stable_fiber_class_lift (d : ℤ)
    (z : stableHomotopyGroup (homotopyFiber (mappingConeInclusion f)) d) :
    ∃ x : stableHomotopyGroup E d,
      (stableHomotopyFunctor d).map (mappingConeFiberComparison f) x = z ∧
      (stableHomotopyFunctor d).map f x =
        (stableHomotopyFunctor d).map (homotopyFiberProjection (mappingConeInclusion f)) z := by
  obtain ⟨x, hx⟩ := ((ConcreteCategory.isIso_iff_bijective _).mp
    (mappingConeFiberComparison_isStableEquivalence_of_positiveLevel f hE hF hf d)).surjective z
  refine ⟨x, hx, ?_⟩
  have he := congrArg ((stableHomotopyFunctor d).map) (mappingConeFiberComparison_projection f)
  rw [Functor.map_comp] at he
  exact (ConcreteCategory.congr_hom he x).symm.trans (congrArg
    ((stableHomotopyFunctor d).map (homotopyFiberProjection (mappingConeInclusion f))) hx)

end Quillen.Tests.ConeFiberWeakEquivalence
