/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module
public import Mathlib.Topology.Path

/-!
# Whole path reconstruction from the two literal half slices, including their midpoint

Intended upstream module: `Aglib.Topology.Path.CarrierHalfPaths`.

For any topological space and continuous interval path, the two literal half paths reconstruct
every value, including their common midpoint. No comparison hypothesis is needed.

Current coefficient-seed and mixed-route consumers:
`CoefficientBassPositiveC1ReassociationPieces`,
`CoefficientBassPositiveC1ShiftedReassociationPieces`.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Topology unitInterval
universe u
namespace Path.CarrierHalfPaths
variable {X : Type u} [TopologicalSpace X]

/-- The original first-half clock, including both endpoints. -/
def lower (s : I) : I := ⟨(s : ℝ) / 2, by constructor <;> linarith [s.2.1, s.2.2]⟩
/-- The original second-half clock, including the shared midpoint. -/
def upper (s : I) : I := ⟨((s : ℝ) + 1) / 2, by constructor <;> linarith [s.2.1, s.2.2]⟩
/-- The shared midpoint of the original unit interval. -/
def middle : I := ⟨1 / 2, by norm_num⟩

/-- The literal first half of an arbitrary continuous path parameter. -/
def first (p : C(I, X)) : Path (p 0) (p middle) where
  toFun s := p (lower s)
  continuous_toFun := p.continuous.comp (by unfold lower; fun_prop)
  source' := congrArg p (by apply Subtype.ext; norm_num [lower])
  target' := congrArg p (by apply Subtype.ext; norm_num [lower, middle])

/-- The literal second half, with the same shared midpoint. -/
def last (p : C(I, X)) : Path (p middle) (p 1) where
  toFun s := p (upper s)
  continuous_toFun := p.continuous.comp (by unfold upper; fun_prop)
  source' := congrArg p (by apply Subtype.ext; norm_num [upper, middle])
  target' := congrArg p (by apply Subtype.ext; norm_num [upper])

/-- The two halves reconstruct every original value; the original clock is unchanged. -/
theorem trans_apply (p : C(I, X)) (s : I) :
    ((first p).trans (last p)) s = p s := by
  rw [Path.trans_apply]
  split_ifs
  · change p (lower _) = p s
    apply congrArg p
    apply Subtype.ext
    dsimp [lower]
    ring
  · change p (upper _) = p s
    apply congrArg p
    apply Subtype.ext
    dsimp [upper]
    ring

end Path.CarrierHalfPaths
