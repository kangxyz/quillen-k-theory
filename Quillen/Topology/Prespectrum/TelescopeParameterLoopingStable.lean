/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.TelescopeParameterLooping
public import Quillen.Topology.Prespectrum.TelescopeStableColimit
public import Quillen.Topology.Prespectrum.StableShift
public import Quillen.Topology.Prespectrum.ConeLoopSeparation

/-!
# Stable equivalence of the original telescope-loop comparison

The actual cylinder comparison is conjugate to the colimit of the original signed loop-shift
isomorphisms. The proof retains its exact stage-inclusion equation in every integer degree.
Only T1 original stages are used, through the proved actual telescope stable-colimit theorem.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
universe u
namespace Quillen.LoopPrespectrum.Telescope
variable (E : ℕ → LoopPrespectrum.{u}) (f : ∀ i, E i ⟶ E (i + 1))

/-- The actual signed loop shifts respect the unchanged original stage transitions. -/
def parameterLoopingStageShift (d : ℤ) :
    stageStableDiagram (fun i => parameterLooping (E i))
        (fun i => parameterLoopingMap (f i)) d ⟶ stageStableDiagram E f (d + 1) :=
  NatTrans.ofSequence (fun i => (parameterStableHomotopyIso (E i) d).hom) (fun i => by
    simpa only [stageStableDiagram, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ] using
      parameterStableHomotopyIso_naturality (f i) d)

/-- This is the same original signed isomorphism at each stage, including its actual sign. -/
theorem parameterLoopingStageShift_app (d : ℤ) (i : ℕ) :
    (parameterLoopingStageShift E f d).app i = (parameterStableHomotopyIso (E i) d).hom := rfl

instance parameterLoopingStageShift_isIso (d : ℤ) : IsIso (parameterLoopingStageShift E f d) := by
  have h (i : ℕ) : IsIso ((parameterLoopingStageShift E f d).app i) := by
    rw [parameterLoopingStageShift_app]
    infer_instance
  let := h
  exact NatIso.isIso_of_isIso_app _

/-- The canonical colimit identity concerns the stable map of the literal cylinder comparison. -/
theorem parameterLoopingComparison_stableColimit (d : ℤ) :
    colimMap (parameterLoopingStageShift E f d) ≫ stableColimitComparison E f (d + 1) =
      stableColimitComparison (fun i => parameterLooping (E i))
        (fun i => parameterLoopingMap (f i)) d ≫
        (stableHomotopyFunctor d).map (parameterLoopingComparison E f) ≫
        (parameterStableHomotopyIso (prespectrum E f) d).hom := by
  apply colimit.hom_ext
  intro i
  rw [ι_colimMap_assoc, parameterLoopingStageShift_app, stableColimitComparison_ι,
    stableColimitComparison_ι_assoc]
  rw [← Category.assoc, ← Functor.map_comp, inclusion_parameterLoopingComparison]
  exact (parameterStableHomotopyIso_naturality (inclusion E f i) d).symm

variable [∀ i k, T1Space ((E i).space k)]

/-- The actual telescope-loop map is conjugate to the colimit of the genuine signed shifts. -/
theorem parameterLoopingComparison_stableMap (d : ℤ) :
    (stableHomotopyFunctor d).map (parameterLoopingComparison E f) =
      (stableColimitIso (fun i => parameterLooping (E i))
        (fun i => parameterLoopingMap (f i)) d).inv ≫
        colimMap (parameterLoopingStageShift E f d) ≫
        (stableColimitIso E f (d + 1)).hom ≫
        (parameterStableHomotopyIso (prespectrum E f) d).inv := by
  apply (cancel_epi (stableColimitIso (fun i => parameterLooping (E i))
    (fun i => parameterLoopingMap (f i)) d).hom).1
  apply (cancel_mono (parameterStableHomotopyIso (prespectrum E f) d).hom).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  exact (parameterLoopingComparison_stableColimit E f d).symm

/-- T1 original stages suffice for stable equivalence in every signed degree. -/
theorem parameterLoopingComparison_isStableEquivalence :
    IsStableEquivalence (parameterLoopingComparison E f) := by
  intro d
  rw [parameterLoopingComparison_stableMap]
  change IsIso (_ ≫ colim.map (parameterLoopingStageShift E f d) ≫ _ ≫ _)
  infer_instance

end Quillen.LoopPrespectrum.Telescope
