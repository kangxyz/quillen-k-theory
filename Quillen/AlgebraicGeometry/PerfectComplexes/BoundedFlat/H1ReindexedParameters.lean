/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module
public import Quillen.AlgebraicGeometry.PerfectComplexes.BoundedFlat.H1SupportOrder

/-! Pure original scalar component parameters in the checked common 130-simplex coordinates. -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open Convexity
open scoped Topology unitInterval
universe u
namespace Quillen.PerfectComplexes.BassH1Order

/-- The old positive parameter transported by `oldIndex` into the common 131-slot simplex. -/
def plusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 131)) :=
  ⟨fun z ↦ StdSimplex.map oldIndex (BassSupportOrder.plusParameter z), by fun_prop⟩

/-- The old inverse parameter transported by `oldIndex` into the common 131-slot simplex. -/
def minusParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 131)) :=
  ⟨fun z ↦ StdSimplex.map oldIndex (BassSupportOrder.minusParameter z), by fun_prop⟩

/-- The old bottom parameter transported by `oldIndex` into the common 131-slot simplex. -/
def bottomParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 131)) :=
  ⟨fun z ↦ StdSimplex.map oldIndex (BassSupportOrder.bottomParameter.{u} z), by fun_prop⟩

/-- The old H0 parameter transported by `oldIndex` into the common 131-slot simplex. -/
def h0Parameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 131)) :=
  ⟨fun z ↦ StdSimplex.map oldIndex (BassSupportOrder.h0Parameter z), by fun_prop⟩

/--
The H0 diagram parameter in the first H1 component, transported to the common simplex by
`firstIndex`.
-/
def firstParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 131)) :=
  ⟨fun z ↦ StdSimplex.map firstIndex (BassH0Diagram.parameter z), by fun_prop⟩

/--
The H0 diagram parameter in the middle H1 component, transported to the common simplex by
`middleIndex`.
-/
def middleParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 131)) :=
  ⟨fun z ↦ StdSimplex.map middleIndex (BassH0Diagram.parameter z), by fun_prop⟩

/-- The positive H1 product parameter transported to the common simplex by `plusProductIndex`. -/
def plusProductParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 131)) :=
  ⟨fun z ↦ StdSimplex.map plusProductIndex (BassH1Components.plusParameter.{u} z), by fun_prop⟩

/-- The inverse H1 product parameter transported to the common simplex by `minusProductIndex`. -/
def minusProductParameter : C(unitInterval × unitInterval, StdSimplex ℝ (Fin 131)) :=
  ⟨fun z ↦ StdSimplex.map minusProductIndex (BassH1Components.minusParameter.{u} z), by fun_prop⟩

end Quillen.PerfectComplexes.BassH1Order
