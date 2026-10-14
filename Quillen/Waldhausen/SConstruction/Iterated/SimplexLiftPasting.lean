/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz, Codex
-/
module

public import Quillen.Waldhausen.SConstruction.Iterated.SimplexLiftReassociation
public import Quillen.Topology.Prespectrum.RelativeHomotopyThreeRoutes

/-! Actual parameter rotation and pasting use exactly the old cancellation and time operations. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory Convexity Quillen.LoopPrespectrum Quillen.Waldhausen.IteratedS
open scoped Topology unitInterval
universe u
namespace Quillen.SimplexParameters
variable {k : ℕ}
  {a b c d : StdSimplex ℝ (Fin (k + 1))}

def reverseCancellation (p : Path a b) :
    (Path.refl b).Homotopy (p.symm.trans p) :=
  (Path.Homotopy.reflTransSymm p.symm).cast rfl
    (congrArg (fun q ↦ p.symm.trans q) (Path.symm_symm p))

/-- Scalar rotation with the exact eight native relative comparisons and their associations. -/
def rotate {p : Path a b} {q : Path b d} {z : Path a c} {w : Path c d}
    (J : (p.trans q).Homotopy (z.trans w)) :
    (p.symm.trans z).Homotopy (q.trans w.symm) := by
  let j1 := (Path.Homotopy.refl p.symm).hcomp (Path.Homotopy.transRefl z).symm
  let j2 := (Path.Homotopy.refl p.symm).hcomp
    ((Path.Homotopy.refl z).hcomp (Path.Homotopy.reflTransSymm w))
  let j3 := (Path.Homotopy.refl p.symm).hcomp (Path.Homotopy.transAssoc z w w.symm).symm
  let j4 := (Path.Homotopy.refl p.symm).hcomp (J.symm.hcomp (Path.Homotopy.refl w.symm))
  let j5 := (Path.Homotopy.transAssoc p.symm (p.trans q) w.symm).symm
  let j6 := ((Path.Homotopy.transAssoc p.symm p q).symm).hcomp (Path.Homotopy.refl w.symm)
  let j7 := ((reverseCancellation p).symm.hcomp (Path.Homotopy.refl q)).hcomp
    (Path.Homotopy.refl w.symm)
  let j8 := (Path.Homotopy.reflTrans q).hcomp (Path.Homotopy.refl w.symm)
  exact j1.trans (j2.trans (j3.trans (j4.trans (j5.trans (j6.trans (j7.trans j8))))))

variable {V W : Model.{u}} (S : ModelSimplex V W k)
  {A B C D : prespectrum V ⟶ prespectrum W}

/-- Native endpoint equality casts do not change a full parameter lift. -/
theorem HomotopyLift.nativeCast {p q : Path a b} {J : p.Homotopy q}
    {H H' K K' : Homotopy A B} {M : H.RelHomotopy K} (hJ : HomotopyLift S J M)
    (hH : H = H') (hK : K = K') (he : H.RelHomotopy K = H'.RelHomotopy K') :
    HomotopyLift S J (he.mp M) := by
  subst H'
  subst K'
  exact hJ

/-- Parameter endpoint casts also preserve every point of the chosen surface. -/
theorem HomotopyLift.parameterCast {p q p' q' : Path a b} {J : p.Homotopy q}
    {H K : Homotopy A B} {M : H.RelHomotopy K} (hJ : HomotopyLift S J M)
    (hp : p = p') (hq : q = q') : HomotopyLift S (J.cast hp hq) M := hJ

/-- The actual rotated native comparison is exactly the scalar rotation, at every whole level. -/
theorem HomotopyLift.rotate {p : Path a b} {q : Path b d} {z : Path a c} {w : Path c d}
    {J : (p.trans q).Homotopy (z.trans w)}
    {H : Homotopy A B} {K : Homotopy B D} {L : Homotopy A C} {M : Homotopy C D}
    {N : (H.trans K).RelHomotopy (L.trans M)}
    (hp : PathLift S p H) (hq : PathLift S q K) (hz : PathLift S z L)
    (hw : PathLift S w M) (hJ : HomotopyLift S J N) :
    HomotopyLift S (rotate J) (Homotopy.RelHomotopy.rotate N) := by
  have h1 := HomotopyLift.hcomp S (PathLift.refl S (PathLift.symm S hp))
    (HomotopyLift.symm S (PathLift.transRefl S hz))
  have h2 := HomotopyLift.hcomp S (PathLift.refl S (PathLift.symm S hp))
    (HomotopyLift.hcomp S (PathLift.refl S hz) (PathLift.reflTransSymm S hw))
  have h3 := HomotopyLift.hcomp S (PathLift.refl S (PathLift.symm S hp))
    (HomotopyLift.symm S (PathLift.transAssoc S hz hw (PathLift.symm S hw)))
  have h4 := HomotopyLift.hcomp S (PathLift.refl S (PathLift.symm S hp))
    (HomotopyLift.hcomp S (HomotopyLift.symm S hJ) (PathLift.refl S (PathLift.symm S hw)))
  have h5 := HomotopyLift.symm S (PathLift.transAssoc S (PathLift.symm S hp)
    (PathLift.trans S hp hq) (PathLift.symm S hw))
  have h6 := HomotopyLift.hcomp S
    (HomotopyLift.symm S (PathLift.transAssoc S (PathLift.symm S hp) hp hq))
    (PathLift.refl S (PathLift.symm S hw))
  have h7 := HomotopyLift.hcomp S
    (HomotopyLift.hcomp S (HomotopyLift.symm S (PathLift.reflSymmTrans S hp))
      (PathLift.refl S hq)) (PathLift.refl S (PathLift.symm S hw))
  have h8 := HomotopyLift.hcomp S (PathLift.reflTrans S hq) (PathLift.refl S (PathLift.symm S hw))
  exact HomotopyLift.trans S h1 (HomotopyLift.trans S h2 (HomotopyLift.trans S h3
    (HomotopyLift.trans S h4 (HomotopyLift.trans S h5 (HomotopyLift.trans S h6
      (HomotopyLift.trans S h7 h8))))))

end Quillen.SimplexParameters
