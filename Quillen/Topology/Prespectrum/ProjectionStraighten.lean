/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Topology.Prespectrum.RelativeHomotopySquarePasting

/-! The literal scalar word of the original two-projection-square pasting. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.Homotopy.RelHomotopy
variable {E F : LoopPrespectrum.{u}}
/-- An exact naming of the unchanged local native straightening subexpression. -/
def projectionStraighten {x y z w : E ⟶ F} {D : Homotopy x y} {A : Homotopy y w}
    {T : Homotopy x z} {K : Homotopy z w} (J : A.RelHomotopy (D.symm.trans (T.trans K))) :
    (D.trans A).RelHomotopy (T.trans K) :=
  ((refl D).hcomp J).trans
    ((transAssoc D D.symm (T.trans K)).symm.trans
      (((reflTransSymm D).symm.hcomp (refl (T.trans K))).trans (reflTrans (T.trans K))))
end Quillen.LoopPrespectrum.Homotopy.RelHomotopy
