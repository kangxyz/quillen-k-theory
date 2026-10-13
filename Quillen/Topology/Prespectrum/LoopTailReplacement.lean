/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.StableStabilization
public import Quillen.Topology.Prespectrum.TelescopeStableColimit
public import Quillen.CategoryTheory.Limits.SequentialIsoColimit
public import Quillen.Topology.Path.Separation

/-!
# A stable-group preserving loop-tail telescope

Iterate the actual loop-tail construction and its original stabilization maps, then form their
existing reduced telescope. Under T1 separation of the original levels, the actual initial-stage
inclusion induces an isomorphism on every integer stable group. The comparison uses the original
telescope colimit map and the proved original stabilization equivalences.

No increasing connectivity, Omega property, cone preservation, or general stable-excision theorem
is asserted for this construction.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u

namespace Quillen.LoopPrespectrum

/-- Iteration uses the existing untransposed loop-tail construction literally. -/
def loopTailIterate (E : LoopPrespectrum.{u}) : ℕ → LoopPrespectrum.{u}
  | 0 => E
  | n + 1 => looping (tail (loopTailIterate E n))

/-- The transitions are precisely the existing original stabilization maps. -/
def loopTailTransition (E : LoopPrespectrum.{u}) (n : ℕ) :
    loopTailIterate E n ⟶ loopTailIterate E (n + 1) :=
  stabilizationMap (loopTailIterate E n)

/-- The actual reduced telescope of the original loop-tail stabilization sequence. -/
def loopTailReplacement (E : LoopPrespectrum.{u}) : LoopPrespectrum.{u} :=
  Telescope.prespectrum (loopTailIterate E) (loopTailTransition E)

/-- The original spectrum enters by its literal zeroth-stage telescope inclusion. -/
def loopTailReplacementInclusion (E : LoopPrespectrum.{u}) : E ⟶ loopTailReplacement E :=
  Telescope.inclusion (loopTailIterate E) (loopTailTransition E) 0

/-- Every transition retains the actual all-integer stable equivalence already proved. -/
theorem loopTailTransition_isStableEquivalence (E : LoopPrespectrum.{u}) (n : ℕ) :
    IsStableEquivalence (loopTailTransition E n) :=
  stabilizationMap_isStableEquivalence (loopTailIterate E n)

variable (E : LoopPrespectrum.{u}) [∀ k, T1Space (E.space k)]

instance loopTailIterate_t1Space (n k : ℕ) : T1Space ((loopTailIterate E n).space k) := by
  induction n generalizing k with
  | zero => exact inferInstanceAs (T1Space (E.space k))
  | succ n ih =>
    let := ih (k + 1)
    exact inferInstanceAs (T1Space (Path ((loopTailIterate E n).point (k + 1))
      ((loopTailIterate E n).point (k + 1))))

/-- The stage stable diagram consists of the actual original stabilization isomorphisms. -/
instance loopTailStableDiagram_succ_isIso (d : ℤ) (n : ℕ) :
    IsIso ((Telescope.stageStableDiagram (loopTailIterate E) (loopTailTransition E) d).map
      (homOfLE (Nat.le_succ n))) := by
  change IsIso ((stableHomotopyFunctor d).map
    ((Functor.ofSequence (loopTailTransition E)).map (homOfLE (Nat.le_succ n))))
  rw [Functor.ofSequence_map_homOfLE_succ]
  exact loopTailTransition_isStableEquivalence E n d

/-- The comparison is assembled from the actual initial-stage and telescope-colimit maps. -/
def loopTailReplacementStableHomotopyIso (d : ℤ) :
    stableHomotopyGroup E d ≅ stableHomotopyGroup (loopTailReplacement E) d :=
  (SequentialIsoColimit.colimitIsoOfSucc
    (Telescope.stageStableDiagram (loopTailIterate E) (loopTailTransition E) d)).symm ≪≫
      Telescope.stableColimitIso (loopTailIterate E) (loopTailTransition E) d

/-- Its forward arrow is exactly the stable map of the original zeroth-stage inclusion. -/
@[simp]
theorem loopTailReplacementStableHomotopyIso_hom (d : ℤ) :
    (loopTailReplacementStableHomotopyIso E d).hom =
      (stableHomotopyFunctor d).map (loopTailReplacementInclusion E) := by
  let D := Telescope.stageStableDiagram (loopTailIterate E) (loopTailTransition E) d
  have hi : (SequentialIsoColimit.colimitIsoOfSucc D).inv = colimit.ι D 0 := by
    apply (cancel_mono (SequentialIsoColimit.colimitIsoOfSucc D).hom).mp
    rw [Iso.inv_hom_id, SequentialIsoColimit.ι_colimitIsoOfSucc_hom]
    rfl
  change (SequentialIsoColimit.colimitIsoOfSucc D).inv ≫
    (Telescope.stableColimitIso (loopTailIterate E) (loopTailTransition E) d).hom = _
  rw [hi]
  exact Telescope.stableColimitIso_ι_hom (loopTailIterate E) (loopTailTransition E) d 0

/-- The actual loop-tail telescope preserves every original signed stable group via its
unchanged initial-stage inclusion, with no connectivity-growth premise. -/
theorem loopTailReplacementInclusion_isStableEquivalence :
    IsStableEquivalence (loopTailReplacementInclusion E) := by
  intro d
  rw [← loopTailReplacementStableHomotopyIso_hom]
  infer_instance

end Quillen.LoopPrespectrum
