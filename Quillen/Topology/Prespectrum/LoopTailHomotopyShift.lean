/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.HomotopyStructure
public import Quillen.Topology.Prespectrum.LoopTailReplacement
public import Quillen.Topology.Prespectrum.TelescopeHomotopyColimit

/-!
# Original homotopy-set interleaving for the loop-tail tower

At a fixed spectrum level and any finite homotopy degree, including zero, the original structure
maps compare the two actual telescope homotopy-set diagrams. The genuine loop shift supplies
return maps to the next original stage. Both successor identities are proved, giving an explicit
isomorphism on the actual colimits. This is based at the displayed chosen points; no conclusion
at other components or Omega-spectrum assertion is supplied here.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits

universe u

namespace Quillen.LoopPrespectrum

variable (E : LoopPrespectrum.{u}) (k n : ℕ)

/-- The original stage structure maps on the actual finite homotopy-set diagrams. -/
def loopTailHomotopyStructureMap :
    Telescope.homotopyDiagram (loopTailIterate E) (loopTailTransition E) k n ⟶
      Telescope.homotopyDiagram (loopTailIterate E) (loopTailTransition E) (k + 1) (n + 1) :=
  NatTrans.ofSequence (fun i ↦ TypeCat.ofHom (structureHomotopyMap (loopTailIterate E i) k n)) (by
    intro i
    ext a
    exact structureHomotopyMap_naturality
      (Telescope.transition (loopTailIterate E) (loopTailTransition E)
        i (i + 1) (Nat.le_succ i)) k n a)

/-- The actual degree shift returns to the next unchanged original loop-tail stage. -/
def loopTailHomotopyReturn (i : ℕ) :
    (Telescope.homotopyDiagram (loopTailIterate E) (loopTailTransition E) (k + 1) (n + 1)).obj i ⟶
      (Telescope.homotopyDiagram (loopTailIterate E) (loopTailTransition E) k n).obj (i + 1) :=
  TypeCat.ofHom (loopShiftEquiv n)

/-- The first successor identity keeps the exact original stabilization transition. -/
theorem loopTailHomotopyStructureMap_return (i : ℕ) :
    (loopTailHomotopyStructureMap E k n).app i ≫ loopTailHomotopyReturn E k n i =
      (Telescope.homotopyDiagram (loopTailIterate E) (loopTailTransition E) k n).map
        (homOfLE (Nat.le_succ i)) := by
  ext a
  change loopShiftEquiv n ((loopShiftEquiv n).symm
    (homotopyGroupMap ((loopTailIterate E i).structureMap k) _ a)) =
      homotopyGroupMap ((Telescope.transition (loopTailIterate E) (loopTailTransition E)
        i (i + 1) (Nat.le_succ i)).map k) _ a
  rw [Equiv.apply_symm_apply]
  exact congrArg (fun f : loopTailIterate E i ⟶ loopTailIterate E (i + 1) ↦
    homotopyGroupMap (f.map k) (f.map_point k) a)
      (Telescope.transition_succ (loopTailIterate E) (loopTailTransition E) i).symm

/-- The second successor identity uses the original untransposed loop structure. -/
theorem loopTailHomotopyReturn_structureMap (i : ℕ) :
    loopTailHomotopyReturn E k n i ≫ (loopTailHomotopyStructureMap E k n).app (i + 1) =
      (Telescope.homotopyDiagram (loopTailIterate E) (loopTailTransition E) (k + 1) (n + 1)).map
        (homOfLE (Nat.le_succ i)) := by
  ext a
  change structureHomotopyMap (looping (tail (loopTailIterate E i))) k n (loopShiftEquiv n a) =
    homotopyGroupMap ((Telescope.transition (loopTailIterate E) (loopTailTransition E)
      i (i + 1) (Nat.le_succ i)).map (k + 1)) _ a
  exact (structureHomotopyMap_looping_tail (loopTailIterate E i) k n a).trans
    (congrArg (fun f : loopTailIterate E i ⟶ loopTailIterate E (i + 1) ↦
      homotopyGroupMap (f.map (k + 1)) (f.map_point (k + 1)) a)
        (Telescope.transition_succ (loopTailIterate E) (loopTailTransition E) i).symm)

/-- The unchanged induced colimit map is an isomorphism, including outer homotopy degree zero. -/
def loopTailHomotopyColimitIso :
    colimit (Telescope.homotopyDiagram (loopTailIterate E) (loopTailTransition E) k n) ≅
      colimit (Telescope.homotopyDiagram (loopTailIterate E) (loopTailTransition E)
        (k + 1) (n + 1)) :=
  SequentialInterleaving.colimitIso (loopTailHomotopyStructureMap E k n)
    (loopTailHomotopyReturn E k n) (loopTailHomotopyStructureMap_return E k n)
    (loopTailHomotopyReturn_structureMap E k n)

end Quillen.LoopPrespectrum
