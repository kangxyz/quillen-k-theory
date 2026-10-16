/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Path.SquareProjectionReturn
public import Quillen.Topology.HomotopyGroups.GenLoopSelfTrack

/-! # Exact signed path words and original based-cube specialization -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open scoped Topology
universe u v
namespace QuillenTest.SquareProjectionReturn
variable {X : Type u} [TopologicalSpace X] {a b c d : X}
  (I : Path a b) (A₀ : Path a c) (A₁ : Path b d) (Z : Path c d)
  (J : (I.trans A₁).Homotopy (A₀.trans Z)) (P : Path b a)

/-- The actual square and return give the exact parenthesized inverse word. -/
def original_parenthesized_return :
    ((P.symm.trans A₁).trans (Z.symm.trans A₀.symm)).Homotopy (I.trans P).symm :=
  Path.Homotopy.squareProjectionReturn J P

variable {E : Type v} [TopologicalSpace E] (f : C(E, X))
  {a' b' c' d' : E} (A₀' : Path a' c') (A₁' : Path b' d') (P' : Path b' a')
  (I' : Path (f a') (f b')) (Z' : Path (f c') (f d'))
  (J' : (I'.trans (A₁'.map f.continuous)).Homotopy
    ((A₀'.map f.continuous).trans Z'))

/-- The fine return remains one actual mapped path. -/
def original_fine_return :
    (((P'.symm.trans A₁').map f.continuous).trans
      (Z'.symm.trans (A₀'.map f.continuous).symm)).Homotopy
        (I'.trans (P'.map f.continuous)).symm :=
  Path.Homotopy.squareProjectionReturnMap f A₀' A₁' P' J'

/-- The supplied original composition triangle is reversed, without changing its track. -/
def original_track_reversal (T : Path (f a') (f a'))
    (K : T.Homotopy (I'.trans (P'.map f.continuous))) :
    (((P'.symm.trans A₁').map f.continuous).trans
      (Z'.symm.trans (A₀'.map f.continuous).symm)).Homotopy T.symm :=
  Path.Homotopy.squareProjectionReturnTrack f A₀' A₁' P' J' K

/-- Every intermediate point remains a based cube, retaining the full original spatial boundary. -/
theorem original_cube_boundary {Y : Type v} [TopologicalSpace Y] {y : Y} (n : ℕ)
    {a b c d : GenLoop (Fin (n + 1)) Y y}
    (I : Path a b) (A₀ : Path a c) (A₁ : Path b d) (Z : Path c d)
    (J : (I.trans A₁).Homotopy (A₀.trans Z)) (P : Path b a)
    (r s : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    Path.Homotopy.squareProjectionReturn J P (r, s) z = y :=
  (Path.Homotopy.squareProjectionReturn J P (r, s)).property z hz

end QuillenTest.SquareProjectionReturn
