/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.RelativeHomotopySquarePasting
public import Quillen.Topology.Prespectrum.RelativeHomotopyLevels

/-! Cancel a common outer track when the original source square has a constant cylinder. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.LoopPrespectrum.Homotopy.RelHomotopy
variable {E F : LoopPrespectrum.{u}} {o c d e f m : E ⟶ F}

/-- The constant-source specialization of actual two-square pasting, retaining all tracks. -/
def pasteStrictSourceSquares {T : Homotopy o m}
    {Lp : Homotopy o c} {Pp : Homotopy c d} {Kp : Homotopy m d}
    {Lm : Homotopy o e} {Pm : Homotopy e f} {Km : Homotopy m f}
    (Jp : (Lp.trans Pp).RelHomotopy (T.trans Kp))
    (Jm : (Lm.trans Pm).RelHomotopy (T.trans Km)) :
    (Homotopy.refl o).RelHomotopy
      ((Lp.trans (Pp.trans ((Kp.symm.trans Km).trans Pm.symm))).trans Lm.symm) := by
  let insert {a b : E ⟶ F} (H : Homotopy a b) :
      H.RelHomotopy ((Homotopy.refl a).symm.trans H) :=
    ((reflTrans H).symm).ofLevels H ((Homotopy.refl a).symm.trans H) (fun _ => rfl)
      (fun n => Homotopy.trans_level_congr _ _ _ _ n rfl rfl)
  have J := pasteTwoSquares (Jp.trans (insert (T.trans Kp)))
    (Jm.trans (insert (T.trans Km)))
  apply J.ofLevels
  · intro n
    apply ContinuousMap.ext
    rintro ⟨s, x⟩
    change (Homotopy.refl o).level n (s, x) =
      (((Homotopy.refl o).symm.levelHomotopy n).trans
        ((Homotopy.refl o).levelHomotopy n)) (s, x)
    rw [ContinuousMap.HomotopyRel.trans_apply]
    split <;> rfl
  · intro n
    rfl

end Quillen.LoopPrespectrum.Homotopy.RelHomotopy
