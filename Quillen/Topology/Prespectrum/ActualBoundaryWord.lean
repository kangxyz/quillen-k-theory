/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.Waldhausen.SConstruction.Iterated.SimplexLiftOperations
public import Quillen.Topology.Path.BoundaryOfComparison

/-! Whole-level lift of the literal native moving-square boundary word. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory Convexity Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.Homotopy.RelHomotopy
variable {E F : LoopPrespectrum.{u}} {a b c d : E ⟶ F}

/-- Generic statement of the exact word written in the native coefficient `boundary` definition. -/
def actualBoundaryWord {B : Homotopy a b} {K : Homotopy b c}
    {H : Homotopy a d} {A : Homotopy d c}
    (J : K.RelHomotopy ((B.symm.trans H).trans A)) :
    H.RelHomotopy ((B.trans K).trans A.symm) := by
  have route : (B.trans K).RelHomotopy (H.trans A) :=
    ((refl B).hcomp J).trans
      (((transAssoc B (B.symm.trans H) A).symm).trans
        ((((transAssoc B B.symm H).symm).hcomp (refl A)).trans
          ((((reflTransSymm B).symm.hcomp (refl H)).hcomp (refl A)).trans
            ((reflTrans H).hcomp (refl A)))))
  exact (transRefl H).symm.trans
    (((refl H).hcomp (reflTransSymm A)).trans
      (((transAssoc H A A.symm).symm).trans
        (route.symm.hcomp (refl A.symm))))
end Quillen.LoopPrespectrum.Homotopy.RelHomotopy
