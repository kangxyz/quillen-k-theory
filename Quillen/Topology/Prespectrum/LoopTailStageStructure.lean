/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Prespectrum.LoopTailComponentTranslation

/-!
# The original replacement structure on positive-stage loop components

The original structure adjoint after any positive-stage inclusion is the literal based loop map
of the previous original structure followed by the next-level inclusion. Natural loop-component
translation therefore gives an exact identity on the actual inclusion-induced homotopy maps.
No invertibility of a finite-stage structure map is assumed or asserted.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory
open scoped Topology unitInterval

universe u

namespace Quillen.LoopPrespectrum

variable (E : LoopPrespectrum.{u}) (i k : ℕ)

/-- The actual underlying map whose loop map is the replacement structure on a positive stage. -/
def loopTailStageStructureMap :
    C((loopTailIterate E i).space (k + 1), (loopTailReplacement E).space (k + 1)) :=
  ((Telescope.inclusion (loopTailIterate E) (loopTailTransition E) (i + 1)).map (k + 1)).comp
    ((loopTailIterate E i).structureMap (k + 1))

/-- The underlying original structure-inclusion composite preserves the displayed point. -/
theorem loopTailStageStructureMap_point :
    loopTailStageStructureMap E i k ((loopTailIterate E i).point (k + 1)) =
      (loopTailReplacement E).point (k + 1) := by
  change (Telescope.inclusion (loopTailIterate E) (loopTailTransition E) (i + 1)).map (k + 1)
    ((loopTailIterate E i).structureMap (k + 1) ((loopTailIterate E i).point (k + 1))) = _
  rw [(loopTailIterate E i).map_point]
  exact (Telescope.inclusion (loopTailIterate E) (loopTailTransition E) (i + 1)).map_point (k + 1)

/-- The original replacement structure after the actual stage inclusion is this literal loop map. -/
theorem loopTailStructure_inclusion_eq_loopMap :
    ((loopTailReplacement E).structureMap k).comp
      ((Telescope.inclusion (loopTailIterate E) (loopTailTransition E) (i + 1)).map k) =
      basedLoopMap (loopTailStageStructureMap E i k) (loopTailStageStructureMap_point E i k) := by
  apply ContinuousMap.ext
  intro γ
  apply Path.ext
  funext t
  rfl

/-- Component translation commutes with the original inclusion followed by the original
structure adjoint, retaining the arbitrary original stage loop. -/
theorem loopTailStructure_inclusion_component (n : ℕ)
    (γ : (loopTailIterate E (i + 1)).space k)
    (a : HomotopyGroup.Pi n ((loopTailIterate E (i + 1)).space k)
      ((loopTailIterate E (i + 1)).point k)) :
    homotopyGroupMap ((loopTailReplacement E).structureMap k) rfl
      (homotopyGroupMap
        ((Telescope.inclusion (loopTailIterate E) (loopTailTransition E) (i + 1)).map k) rfl
        (loopComponentHomotopyEquiv γ n a)) =
      loopComponentHomotopyEquiv
        ((loopTailReplacement E).structureMap k
          ((Telescope.inclusion (loopTailIterate E) (loopTailTransition E) (i + 1)).map k γ)) n
        (homotopyGroupMap ((loopTailReplacement E).structureMap k)
          ((loopTailReplacement E).map_point k)
          (homotopyGroupMap
            ((Telescope.inclusion (loopTailIterate E) (loopTailTransition E) (i + 1)).map k)
            ((Telescope.inclusion (loopTailIterate E) (loopTailTransition E) (i + 1)).map_point k)
            a)) := by
  let l := (Telescope.inclusion (loopTailIterate E) (loopTailTransition E) (i + 1)).map k
  let s := (loopTailReplacement E).structureMap k
  let h := loopTailStageStructureMap E i k
  have hl := (Telescope.inclusion (loopTailIterate E) (loopTailTransition E) (i + 1)).map_point k
  have hs := (loopTailReplacement E).map_point k
  have he := loopTailStructure_inclusion_eq_loopMap E i k
  have hn := loopComponentHomotopyEquiv_naturality h
    (loopTailStageStructureMap_point E i k) γ n a
  have hbase : homotopyGroupMap (basedLoopMap h (loopTailStageStructureMap_point E i k))
      (basedLoopMap_refl h (loopTailStageStructureMap_point E i k)) a =
      homotopyGroupMap s hs (homotopyGroupMap l hl a) := by
    exact (congrFun (homotopyGroupMap_congr he.symm
      (basedLoopMap_refl h (loopTailStageStructureMap_point E i k))
      ((congrArg s hl).trans hs)) a).trans (homotopyGroupMap_comp l hl s hs a)
  have hother := congrFun (homotopyGroupMap_congr he rfl rfl)
    (loopComponentHomotopyEquiv γ n a)
  exact (homotopyGroupMap_comp l rfl s rfl (loopComponentHomotopyEquiv γ n a)).symm.trans
    (hother.trans (hn.symm.trans (congrArg (loopComponentHomotopyEquiv (s (l γ)) n) hbase)))

end Quillen.LoopPrespectrum
