/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.HomotopyFiber.GenLoopPathTransport

/-! # Whole source/null transports in the original homotopy fiber -/
set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true
@[expose] public section
noncomputable section
open scoped Topology unitInterval
universe u v
namespace QuillenTest.GenLoopPathTransport
open Quillen Quillen.HomotopyFiber
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (y : Y) (x : X) (h : f x = y) (n : ℕ)
local notation "E" => GenLoop (Fin (n + 1)) X x
local notation "F" => genLoopPostcompContinuousMap (N := Fin (n + 1)) f h
local notation "B" => (GenLoop.const : GenLoop (Fin (n + 1)) Y y)

/-- Both homotopy times and the whole original spatial input survive null-path variation. -/
theorem original_null_variation (p : E) {P Q : Path (F p) B} (J : P.Homotopy Q)
    (s t : unitInterval) (z : Fin (n + 1) → unitInterval) :
    (genLoopNullLiftHomotopy f y x h n p J (s, z)).val.2 t = J (s, t) z := rfl

/-- Reversing the old slide moves along the actual original source path forwards. -/
theorem original_source_slide {p q : E} (D : Path p q) (N : Path (F q) B)
    (s : unitInterval) :
    (genLoopSourceSlidePath f y x h n D N s).val.1 = D s :=
  genLoopSourceSlidePath_source f y x h n D N s

/-- The exact concatenation retains the old slide and the old unit-delay removal separately. -/
theorem original_slide_unpad {p q : E} (D : Path p q) (N : Path (F q) B) :
    genLoopSourceTransportPath f y x h n D N =
      (genLoopSourceSlidePath f y x h n D N).trans
        (genLoopSourceUnpadPath f y x h n D N) := rfl

/-- The full source transport consumes the entire supplied terminal null path. -/
def original_source_transport {p q : E} (D : Path p q) (N : Path (F q) B) :
    (genLoopNullLift f y x h n p ((D.map (F).continuous).trans N)).val.HomotopyRel
      (genLoopNullLift f y x h n q N).val (Cube.boundary (Fin (n + 1))) :=
  genLoopSourceTransportHomotopy f y x h n D N

/-- The original returned loop displays its single reversed image and exact source cast. -/
theorem original_return_word (p : E) (P : Path (F p) B) (rho : Path p GenLoop.const) :
    genLoopReturnedLoop f y x h n p P rho =
      (((rho.map (F).continuous).symm.cast
        (genLoopPostcomp_const f h).symm rfl).trans P) :=
  genLoopReturnedLoop_eq f y x h n p P rho

/-- The original iterated-fiber homotopy gives the entire loop-to-lift comparison. -/
def original_loop_return (p : E) (P : Path (F p) B) (rho : Path p GenLoop.const) :
    (genLoopPostcomp (loopInclusion f y x h) (loopInclusion_refl f y x h)
      (genLoopOfBasedPath (genLoopReturnedLoop f y x h n p P rho))).val.HomotopyRel
        (genLoopNullLift f y x h n p P).val (Cube.boundary (Fin (n + 1))) :=
  genLoopReturnHomotopy f y x h n p P rho

variable {p q : GenLoop (Fin (n + 1)) X x} (D : Path p q)
  (P : Path (genLoopPostcomp f h p) (GenLoop.const : GenLoop (Fin (n + 1)) Y y))
  (N : Path (genLoopPostcomp f h q) (GenLoop.const : GenLoop (Fin (n + 1)) Y y))
  (rho : Path p GenLoop.const)
  (J : P.Homotopy
    ((D.map (genLoopPostcompContinuousMap (N := Fin (n + 1)) f h).continuous).trans N))

include J in
/-- Every original null and comparison remains supplied as data in the complete paste. -/
def original_whole_comparison :
    (genLoopPostcomp (loopInclusion f y x h) (loopInclusion_refl f y x h)
      (genLoopOfBasedPath (genLoopReturnedLoop f y x h n p P rho))).val.HomotopyRel
        (genLoopNullLift f y x h n q N).val (Cube.boundary (Fin (n + 1))) :=
  genLoopReturnComparison f y x h n D P N rho J

include J in
/-- The original first-coordinate degree shift inserts no extra inversion or permutation. -/
def original_loop_curry_comparison :
    (genLoopPostcomp (loopInclusion f y x h) (loopInclusion_refl f y x h)
      (loopCurry (loopUncurry
        (genLoopOfBasedPath (genLoopReturnedLoop f y x h n p P rho))))).val.HomotopyRel
      (genLoopNullLift f y x h n q N).val (Cube.boundary (Fin (n + 1))) := by
  simpa only [loopCurry_loopUncurry] using genLoopReturnComparison f y x h n D P N rho J

/-- Independent homotopy time fixes the complete actual fiber point on every spatial face. -/
theorem original_whole_boundary (s : unitInterval) (z : Fin (n + 1) → unitInterval)
    (hz : z ∈ Cube.boundary (Fin (n + 1))) :
    genLoopReturnComparison f y x h n D P N rho J (s, z) = basepoint f y x h :=
  ((genLoopReturnComparison f y x h n D P N rho J).eq_snd s hz).trans
    ((genLoopNullLift f y x h n q N).property z hz)

/-- The one-coordinate input retains the same actual return, null and full comparison. -/
def original_degree_zero {p₀ q₀ : GenLoop (Fin 1) X x} (D₀ : Path p₀ q₀)
    (P₀ : Path (genLoopPostcomp f h p₀) (GenLoop.const : GenLoop (Fin 1) Y y))
    (N₀ : Path (genLoopPostcomp f h q₀) (GenLoop.const : GenLoop (Fin 1) Y y))
    (rho₀ : Path p₀ GenLoop.const)
    (J₀ : P₀.Homotopy
      ((D₀.map (genLoopPostcompContinuousMap (N := Fin 1) f h).continuous).trans N₀)) :
    (genLoopPostcomp (loopInclusion f y x h) (loopInclusion_refl f y x h)
      (genLoopOfBasedPath (genLoopReturnedLoop f y x h 0 p₀ P₀ rho₀))).val.HomotopyRel
        (genLoopNullLift f y x h 0 q₀ N₀).val (Cube.boundary (Fin 1)) :=
  genLoopReturnComparison f y x h 0 D₀ P₀ N₀ rho₀ J₀

end QuillenTest.GenLoopPathTransport
