/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.Realization.MonomorphismHEP
public import Quillen.Topology.Realization.Homotopy

/-!
# Homotopy extension at actual realized vertices

The inclusion of the literal point represented by a simplicial vertex has the homotopy extension
property. The proof uses the actual monomorphism from the standard zero-simplex and its realized
HEP, with no change of basepoint or homotopy-equivalent replacement of the realization.
-/
@[expose] public section
noncomputable section

open CategoryTheory
open scoped Simplicial Topology unitInterval
universe u
namespace Quillen.Realization

/-- A chosen vertex defines an actual simplicial monomorphism from the zero-simplex. -/
theorem mono_vertex {X : SSet.{u}} (x : X _⦋0⦌) : Mono (SSet.yonedaEquiv.symm x) :=
  SSet.stdSimplex.isTerminalObj₀.mono_from _

/-- The literal realized vertex is a well-based point: its singleton inclusion has HEP. -/
theorem homotopyExtensionProperty_vertex {X : SSet.{u}} (x : X _⦋0⦌) :
    Quillen.homotopyExtensionProperty
      (TopCat.ofHom (ContinuousMap.const PUnit.{u + 1} (realizationPoint x))) := by
  let : Mono (SSet.yonedaEquiv.symm x) := mono_vertex x
  have hi := homotopyExtensionProperty_realization_mono (SSet.yonedaEquiv.symm x)
  apply Quillen.homotopyExtensionProperty_of_continuous
  intro Z f H hzero
  let H' : C(unitInterval × |(Δ[0] : SSet.{u})|, Z) :=
    ⟨fun z ↦ H (z.1, PUnit.unit), by fun_prop⟩
  have hv (a : |(Δ[0] : SSet.{u})|) :
      SSet.toTop.map (SSet.yonedaEquiv.symm x) a = realizationPoint x := by
    exact congrArg (SSet.toTop.map (SSet.yonedaEquiv.symm x)) (Subsingleton.elim a default)
  obtain ⟨K, hKzero, hK⟩ := Quillen.homotopyExtensionProperty_continuous hi Z f H' (by
    intro a
    change H (0, PUnit.unit) = f (SSet.toTop.map (SSet.yonedaEquiv.symm x) a)
    rw [hv]
    exact hzero PUnit.unit)
  refine ⟨K, hKzero, ?_⟩
  intro t a
  cases a
  exact hK t default

end Quillen.Realization
