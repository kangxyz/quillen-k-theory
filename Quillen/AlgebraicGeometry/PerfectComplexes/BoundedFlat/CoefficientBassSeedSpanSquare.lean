/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Quillen.Topology.Prespectrum.RelativeHomotopySquarePasting
public import Quillen.Topology.Prespectrum.HomotopySquareOfPasting

/-! Turn the actual equal-composite boundary comparison into a moving leg square. -/
@[expose] public section
noncomputable section
open CategoryTheory
universe u
namespace Quillen.PerfectComplexes.CoefficientBassSeedSpanSquare
open Quillen.LoopPrespectrum Quillen.LoopPrespectrum.Homotopy
open Quillen.LoopPrespectrum.Homotopy.RelHomotopy
variable {E F : LoopPrespectrum.{u}} {a b c d e f : E ⟶ F}

/-- Cancel only the final inverse edge using its original relative contraction. -/
def closeRight {H : Homotopy a b} {A : Homotopy a c} {B : Homotopy b c}
    (J : H.RelHomotopy (A.trans B.symm)) : (H.trans B).RelHomotopy A :=
  (J.hcomp (refl B)).trans
    ((transAssoc A B.symm B).trans
      (((refl A).hcomp (reflSymmTrans B).symm).trans (transRefl A)))

/-- The whole boundary comparison supplies the square of the two actual span leg tracks. -/
def square {H : Homotopy a b} {L : Homotopy a c} {P : Homotopy c d}
    {K : Homotopy d f} {M : Homotopy e f} {N : Homotopy b e}
    (J : H.RelHomotopy ((L.trans (P.trans (K.trans M.symm))).trans N.symm)) :
    (H.trans N).Square (P.trans K) L M :=
  ((closeRight J).trans
    (((refl L).hcomp (transAssoc P K M.symm).symm).trans
      (transAssoc L (P.trans K) M.symm).symm)).toSquare

end Quillen.PerfectComplexes.CoefficientBassSeedSpanSquare
