/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.MScalarPasting

/-! The eight original whole scalar joins survive the same exact finite relabeling. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Convexity
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassMScalarPasting
variable {k : ℕ} (g : Fin 131 → Fin (k + 1))

theorem h0_plus_scalar (s : unitInterval) : h0 g (s, 0) = plus g (0, s) :=
  congrArg (StdSimplex.map g) (BassH1Merged.h0_plus_scalar s)

theorem h0_minus_scalar (s : unitInterval) : h0 g (s, 1) = minus g (0, s) :=
  congrArg (StdSimplex.map g) (BassH1Merged.h0_minus_scalar s)

theorem h0_bottom_scalar (t : unitInterval) : h0 g (0, t) = bottom.{u} g (0, t) :=
  congrArg (StdSimplex.map g) (BassH1Merged.h0_bottom_scalar.{u} t)

theorem plus_bottom_scalar (r : unitInterval) : plus g (r, 0) = bottom.{u} g (r, 0) :=
  congrArg (StdSimplex.map g) (BassH1Merged.plus_bottom_scalar.{u} r)

theorem minus_bottom_scalar (r : unitInterval) : minus g (r, 0) = bottom.{u} g (r, 1) :=
  congrArg (StdSimplex.map g) (BassH1Merged.minus_bottom_scalar.{u} r)

theorem h1_plus_scalar (s : unitInterval) : h1.{u} g (s, 0) = plus g (1, s) :=
  congrArg (StdSimplex.map g) (BassH1Merged.h1_plus_scalar.{u} s)

theorem h1_minus_scalar (s : unitInterval) : h1.{u} g (s, 1) = minus g (1, s) :=
  congrArg (StdSimplex.map g) (BassH1Merged.h1_minus_scalar.{u} s)

theorem h1_bottom_scalar (t : unitInterval) : h1.{u} g (0, t) = bottom.{u} g (1, t) :=
  congrArg (StdSimplex.map g) (BassH1Merged.h1_bottom_scalar.{u} t)

end Quillen.PerfectComplexes.BassMScalarPasting
