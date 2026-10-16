/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.SelfTrackHomotopyClass

/-! Original finite track classes retain representatives and their relative homotopies. -/
@[expose] public section
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true

open CategoryTheory
open Quillen Quillen.LoopPrespectrum
universe u
namespace QuillenTest.SelfTrackHomotopyClass

/-- The quotient operation agrees on any two actual homotopic input cubes. -/
theorem original_homotopic_representatives {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n m : ℕ)
    {p q : GenLoop (Fin (m + 1)) (E.space n) (E.point n)} (h : GenLoop.Homotopic p q) :
    H.homotopyClassOperation n m ⟦p⟧ =
      genLoopSelfTrackClass m _ (H.genLoopPath n q) :=
  H.genLoopSelfTrackClass_congr n m h

/-- With the old one-higher vanishing hypothesis the entire quotient function is constant. -/
theorem original_vanishing_operation {E F : LoopPrespectrum.{u}} {f : E ⟶ F}
    (H : Homotopy f f) (n m : ℕ)
    (hF : Subsingleton (HomotopyGroup.Pi (m + 2) (F.space n) (F.point n)))
    (a : HomotopyGroup.Pi (m + 1) (E.space n) (E.point n)) :
    H.homotopyClassOperation n m a = 1 := hF.elim _ _

end QuillenTest.SelfTrackHomotopyClass
