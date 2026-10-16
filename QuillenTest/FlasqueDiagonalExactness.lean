/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.AlgebraicGeometry.PerfectComplexes.ProjectiveLine.FlasqueDiagonalExact

/-! # Exact original flasque diagonal map consumers

The original raw functor preserves the first and last arrows of each specified
short exact sequence. The lifted vertex functor preserves the four actual maps
of each pushout along an inherited model cofibration, over every base ring.
-/
@[expose] public section

set_option warningAsError true
set_option autoImplicit false
set_option linter.mathlibStandardSet true

noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Quillen.PerfectComplexes AlgebraicGeometry.Scheme.ProjectiveLine
open Quillen.PerfectComplexes.ProjectiveLine.FlasqueDiagonal

namespace FlasqueDiagonalExactnessConsumers

/-- The actual raw first arrow is monic, without replacing its coefficient or total. -/
theorem original_raw_first_mono (R : CommRingCat.{u}) (v : Vertex)
    (S : ShortComplex (FlasqueBoundedBelow.Obj (twoChartLine R)))
    (hS : (S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact) :
    Mono ((raw R v).map S.f) :=
  (raw_shortExact R v S hS).mono_f

/-- The actual raw last arrow is epic, using the original flasque-kernel exactness. -/
theorem original_raw_last_epi (R : CommRingCat.{u}) (v : Vertex)
    (S : ShortComplex (FlasqueBoundedBelow.Obj (twoChartLine R)))
    (hS : (S.map (FlasqueBoundedBelow.objects (twoChartLine R)).ι).ShortExact) :
    Epi ((raw R v).map S.g) :=
  (raw_shortExact R v S hS).epi_g

/-- Each inherited admissible pushout retains all four original vertex maps. -/
theorem original_vertex_pushout (R : CommRingCat.{u}) (v : Vertex)
    {A B D T : FlasqueBoundedBelow.Obj (twoChartLine R)}
    {i : A ⟶ B} {f : A ⟶ D} {g : B ⟶ T} {j : D ⟶ T}
    (hi : (FlasqueBoundedBelow.waldhausen (twoChartLine R)).cof i)
    (h : IsPushout i f g j) :
    IsPushout ((E R v).map i) ((E R v).map f) ((E R v).map g) ((E R v).map j) :=
  (E_exact R v).pushout hi h

end FlasqueDiagonalExactnessConsumers
