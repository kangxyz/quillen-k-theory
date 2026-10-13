/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Quillen.Topology.LocalCoefficients.SupportedChains
public import Quillen.Topology.LocalCoefficients.Homology
public import Mathlib.Algebra.Homology.QuasiIso

/-! # Actual chain inclusion for coefficients supported on a path component -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Quillen.LocalCoefficients

universe u

example {X : Type u} [TopologicalSpace X] (x : X) (A : System.{u, u} X)
    (hA : ∀ y, y ∉ pathComponent x → IsZero (fiber A y)) :
    IsIso (pushforwardChainMap (subspaceInclusion (pathComponent x)) A) :=
  pathComponentInclusion_pushforwardChainMap_isIso_of_support x A hA

example {X : Type u} [TopologicalSpace X] (x : X) (A : System.{u, u} X)
    (hA : ∀ y, y ∉ pathComponent x → IsZero (fiber A y)) :
    QuasiIso
      (pushforwardChainMap (subspaceInclusion (pathComponent x)) A) := by
  have := pathComponentInclusion_pushforwardChainMap_isIso_of_support x A hA
  infer_instance
