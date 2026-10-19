/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Quillen.Topology.Prespectrum.RowNormalization
public import Quillen.Topology.Prespectrum.RelativeHomotopyConjugation
public import Quillen.Topology.Prespectrum.RelativeHomotopyLoop

/-!
# Moving-endpoint transport of normalized row operations

The supplied endpoint path and its actual unit-intertwining prism are retained.
The original null is transported along that path, with an explicit cancellation
prism. Whole spectrum normalization on both sides then gives the comparison;
no equality of endpoints or detection by homotopy groups is used.
-/
@[expose] public section
noncomputable section
open CategoryTheory
open scoped Topology unitInterval
universe u
namespace Quillen.LoopPrespectrum.RowRefinement
variable {D E : LoopPrespectrum.{u}}
  (q : ∀ k, C(E.space (k + 3), E.space (k + 3)))
  (hq : ∀ k, q k (E.point (k + 3)) = E.point (k + 3))
  {f g : D ⟶ spectrum E q hq}
  (L : Homotopy f g) (U : Homotopy f f) (V : Homotopy g g)
  (J : (U.trans L).RelHomotopy (L.trans V))
  (N : Homotopy f (zeroHom D (spectrum E q hq)))

/-- Move the original null by the specified endpoint path, without choosing a new contraction. -/
def movedNull : Homotopy g (zeroHom D (spectrum E q hq)) := L.symm.trans N

/-- The null comparison retains the actual endpoint path and its canonical cancellation. -/
def movedNullComparison : N.RelHomotopy (L.trans (movedNull q hq L N)) :=
  ((Homotopy.RelHomotopy.transAssoc L L.symm N).symm.trans
    (((Homotopy.RelHomotopy.reflTransSymm L).symm.hcomp
      (Homotopy.RelHomotopy.refl N)).trans (Homotopy.RelHomotopy.reflTrans N))).symm

/-- The prescribed unit prism gives the whole original null-conjugation comparison. -/
def movedNullLoopHomotopy :
    Homotopy (U.nullLoopMap N) (V.nullLoopMap (movedNull q hq L N)) :=
  (Homotopy.RelHomotopy.conjugateNaturality L U V N (movedNull q hq L N)
    J (movedNullComparison q hq L N)).zeroLoopMapHomotopy

/-- Inverse-prefix normalization respects an actual moving-endpoint prism after the boundary.
-/
def normalizationPasting :
    Homotopy (normalizedOperation q hq f U) (normalizedOperation q hq g V) :=
  (normalizationHomotopy q hq f U N).trans
    ((movedNullLoopHomotopy q hq L U V J N).trans
      (normalizationHomotopy q hq g V (movedNull q hq L N)).symm)

/-- The middle comparison retains independent prism, unit and positive row coordinates. -/
theorem movedNullLoopHomotopy_succ (k : ℕ) (x : D.space (k + 1))
    (r t s : unitInterval) :
    Path.toContinuousMap
      (Path.toContinuousMap ((movedNullLoopHomotopy q hq L U V J N).level (k + 1)
        (r, x)) t) s =
    Path.toContinuousMap
      ((Homotopy.RelHomotopy.conjugateNaturality L U V N (movedNull q hq L N)
        J (movedNullComparison q hq L N)).level (k + 1) (r, (t, x))) s := rfl

/-- Degree zero also retains the original source-loop coordinate. -/
theorem movedNullLoopHomotopy_zero (x : D.space 0) (r t a s : unitInterval) :
    Path.toContinuousMap (Path.toContinuousMap
      (Path.toContinuousMap ((movedNullLoopHomotopy q hq L U V J N).level 0 (r, x)) t)
        a) s =
    Path.toContinuousMap (Path.toContinuousMap
      ((Homotopy.RelHomotopy.conjugateNaturality L U V N (movedNull q hq L N)
        J (movedNullComparison q hq L N)).level 0 (r, (t, x))) a) s := rfl

end Quillen.LoopPrespectrum.RowRefinement
