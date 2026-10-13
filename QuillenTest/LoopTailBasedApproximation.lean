/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.Prespectrum.LoopTailBasedApproximation

/-!
# Original-map consumers of the based loop-tail approximation

The original cube and structure parameter order is retained. Actual based target cubes lift up
to a whole boundary-relative homotopy, and actual homotopies after the structure adjoint reflect
back to the original source cubes. Degree zero also reflects arbitrary source components. These
consumers do not assert positive-degree bijectivity outside the chosen source component.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Quillen Quillen.LoopPrespectrum
open scoped Topology unitInterval

universe u

namespace QuillenTest.LoopTailBasedApproximation

open Quillen

/-- The added first cube coordinate is the original structure time, with no parameter transpose. -/
theorem original_structure_cube_parameters (E : LoopPrespectrum.{u}) (k n : ℕ)
    (p : GenLoop (Fin n) (E.space k) (E.point k)) (z : Fin (n + 1) → unitInterval) :
    loopUncurry (genLoopPostcomp (E.structureMap k) (E.map_point k) p) z =
      E.structureMap k (p (Fin.tail z)) (z 0) := rfl

variable (E : LoopPrespectrum.{u}) [∀ k, T1Space (E.space k)] (k n : ℕ)

/-- Every actual target cube at the chosen loop admits an actual source cube with the whole
required boundary-relative comparison, including outer degree zero. -/
theorem original_based_target_cube_lifts
    (p : GenLoop (Fin n)
      (Path ((loopTailReplacement E).point (k + 1)) ((loopTailReplacement E).point (k + 1)))
      (Path.refl ((loopTailReplacement E).point (k + 1)))) :
    ∃ q : GenLoop (Fin n) ((loopTailReplacement E).space k) ((loopTailReplacement E).point k),
      GenLoop.Homotopic
        (genLoopPostcomp ((loopTailReplacement E).structureMap k)
          ((loopTailReplacement E).map_point k) q) p := by
  obtain ⟨a, ha⟩ := (loopTailReplacement_structureMap_homotopy_bijective E k n).surjective
    (Quotient.mk' p)
  induction a using Quotient.inductionOn with
  | h q => exact ⟨q, Quotient.exact ha⟩

/-- Equality after the original structure map reflects a genuine homotopy of the original based
source cubes, rather than merely equality on stable groups. -/
theorem original_based_source_homotopy_reflected
    (p q : GenLoop (Fin n) ((loopTailReplacement E).space k) ((loopTailReplacement E).point k))
    (H : GenLoop.Homotopic
      (genLoopPostcomp ((loopTailReplacement E).structureMap k)
        ((loopTailReplacement E).map_point k) p)
      (genLoopPostcomp ((loopTailReplacement E).structureMap k)
        ((loopTailReplacement E).map_point k) q)) : GenLoop.Homotopic p q := by
  exact Quotient.exact
    ((loopTailReplacement_structureMap_homotopy_bijective E k n).injective (Quotient.sound H))

/-- The zero-dimensional result reflects arbitrary source components, without asserting
positive-degree tests at those components. -/
theorem original_source_components_reflected
    (x y : (loopTailReplacement E).space k)
    (h : Joined ((loopTailReplacement E).structureMap k x)
      ((loopTailReplacement E).structureMap k y)) : Joined x y := by
  let p : GenLoop (Fin 0) ((loopTailReplacement E).space k) ((loopTailReplacement E).point k) :=
    ⟨ContinuousMap.const _ x, by rintro t ⟨i, _⟩; exact Fin.elim0 i⟩
  let q : GenLoop (Fin 0) ((loopTailReplacement E).space k) ((loopTailReplacement E).point k) :=
    ⟨ContinuousMap.const _ y, by rintro t ⟨i, _⟩; exact Fin.elim0 i⟩
  have H : GenLoop.Homotopic
      (genLoopPostcomp ((loopTailReplacement E).structureMap k)
        ((loopTailReplacement E).map_point k) p)
      (genLoopPostcomp ((loopTailReplacement E).structureMap k)
        ((loopTailReplacement E).map_point k) q) := ⟨{
    toFun z := h.somePath z.1
    continuous_toFun := by fun_prop
    map_zero_left _ := h.somePath.source
    map_one_left _ := h.somePath.target
    prop' := by rintro t s ⟨i, _⟩; exact Fin.elim0 i }⟩
  obtain ⟨K⟩ := original_based_source_homotopy_reflected E k 0 p q H
  exact ⟨K.toHomotopy.evalAt 0⟩

end QuillenTest.LoopTailBasedApproximation
