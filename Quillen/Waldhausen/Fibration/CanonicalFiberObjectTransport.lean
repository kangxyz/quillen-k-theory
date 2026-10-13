/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Waldhausen.Fibration.CanonicalFiberObjectLoop

/-!
# Specified object transport in the original canonical fiber

An actual weak arrow in the relative-acyclic category gives a data-valued transport between
its two original canonical fiber loops. Comparison, object-loop and fiber-path times remain
independent, and the last coordinate uses the original reversed zero-to-inclusion cylinder.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology
universe u v
namespace Quillen.Waldhausen.Fibration
variable {C : Type u} [Category.{v} C] {V : Structure C}
  (N : NestedWeakEquivalences V) {X Y : AcyclicCategory N}
  (f : X ⟶ Y) (hf : (acyclicStructure N).weq f)

/-- Map the specified original weak-arrow track through the actual canonical fiber map. -/
def canonicalFiberObjectWeakTrack :
    (canonicalFiberObjectLoop N X).Homotopy (canonicalFiberObjectLoop N Y) where
  toFun z := canonicalFiberMap N ((acyclicStructure N).weakObjectLoopTrack f hf z)
  continuous_toFun := by fun_prop
  map_zero_left t := by
    rw [Structure.weakObjectLoopTrack_zero]
    rfl
  map_one_left t := by
    rw [Structure.weakObjectLoopTrack_one]
    rfl
  prop' r t ht := by
    rcases ht with ht | ht
    · subst t
      change canonicalFiberMap N ((acyclicStructure N).weakObjectLoopTrack f hf (r, 0)) =
        canonicalFiberObjectLoop N X 0
      rw [Structure.weakObjectLoopTrack_source]
      exact (canonicalFiberMap_basepoint N).trans (Path.source _).symm
    · rw [Set.mem_singleton_iff] at ht
      subst t
      change canonicalFiberMap N ((acyclicStructure N).weakObjectLoopTrack f hf (r, 1)) =
        canonicalFiberObjectLoop N X 1
      rw [Structure.weakObjectLoopTrack_target]
      exact (canonicalFiberMap_basepoint N).trans (Path.target _).symm

/-- The whole transported cylinder is the original canonical map on the original weak track. -/
theorem canonicalFiberObjectWeakTrack_apply (r t : unitInterval) :
    canonicalFiberObjectWeakTrack N f hf (r, t) =
      canonicalFiberMap N ((acyclicStructure N).weakObjectLoopTrack f hf (r, t)) := rfl

/-- Its projection retains the actual fine acyclic inclusion at every independent pair of times.
-/
theorem canonicalFiberObjectWeakTrack_projection (r t : unitInterval) :
    (canonicalFiberObjectWeakTrack N f hf (r, t)).val.1 =
      acyclicInclusionMap N ((acyclicStructure N).weakObjectLoopTrack f hf (r, t)) := rfl

/-- Its original null track remains visible at the third, independent fiber-path time. -/
theorem canonicalFiberObjectWeakTrack_path (r t s : unitInterval) :
    (canonicalFiberObjectWeakTrack N f hf (r, t)).val.2 s =
      acyclicNullhomotopy N (s, (acyclicStructure N).weakObjectLoopTrack f hf (r, t)) := rfl

/-- The fiber coordinate is the specified zero-to-inclusion transformation run backwards. -/
theorem canonicalFiberObjectWeakTrack_path_transformation (r t s : unitInterval) :
    (canonicalFiberObjectWeakTrack N f hf (r, t)).val.2 s =
      weakNaturalTransformationRealizationHomotopy (acyclicStructure N) N.coarse
        (zeroFunctor_isExact _ _) (acyclicInclusion_coarse_exact N)
        (zeroToAcyclicInclusion N) (zeroToAcyclicInclusion_weak N)
        (unitInterval.symm s, (acyclicStructure N).weakObjectLoopTrack f hf (r, t)) := rfl

end Quillen.Waldhausen.Fibration
