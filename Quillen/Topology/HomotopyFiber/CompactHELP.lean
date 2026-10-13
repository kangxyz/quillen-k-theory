/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Quillen.Topology.HomotopyFiber.CompactLifting
public import Quillen.Topology.HELP.CompactLifting

/-! # Genuine compact HELP on actual source-change homotopy fibers

The compact family retains its original path coordinate. The resulting HELP
statement keeps every prescribed boundary homotopy exactly.
-/
@[expose] public section

noncomputable section
open scoped Topology
universe u v w t

namespace Quillen.HomotopyFiber
variable {X : Type u} {Y : Type v} {Z : Type w}
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Exact lifting of the source coordinate works in every parameter universe. -/
theorem sourceMap_lifts (f : C(Y, Z)) (e : C(X, Y))
    (T : Type t) [TopologicalSpace T]
    (hl : ∀ g : C(T, Y), ∃ h : C(T, X), e.comp h = g) (z : Z)
    (g : C(T, HomotopyFiber f z)) :
    ∃ h : C(T, HomotopyFiber (f.comp e) z), (sourceMap f e z).comp h = g := by
  obtain ⟨h, hh⟩ := hl ((projection f z).comp g)
  let k : C(T, HomotopyFiber (f.comp e) z) := {
    toFun t := ⟨(h t, (g t).1.2),
      (g t).2.1.trans (congrArg f (DFunLike.congr_fun hh t)).symm, (g t).2.2⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      apply Continuous.prodMk h.continuous
      fun_prop }
  refine ⟨k, ?_⟩
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  exact _root_.Prod.ext (DFunLike.congr_fun hh t) rfl

/-- Injective exact compact source change gives compact HELP on the actual
homotopy fiber, with no assumed fiber comparison equivalence. -/
theorem sourceMap_compactHELP
    {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (e : C(X, Y)) (he : Function.Injective e)
    (hl : ∀ (T : Type u) [TopologicalSpace T] [CompactSpace T] (g : C(T, Y)),
      ∃ h : C(T, X), e.comp h = g) (z : Z) :
    CompactHomotopyExtensionLiftingProperty (sourceMap f e z) :=
  compactHELP_of_injective_compact_lifts (sourceMap f e z) (sourceMap_injective f e he z)
    (fun T _ _ ↦ sourceMap_lifts f e T (hl T) z)

end Quillen.HomotopyFiber
