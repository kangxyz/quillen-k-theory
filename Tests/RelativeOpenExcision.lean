/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
import Quillen.Topology.LocalCoefficients.OpenExcision
/-! Independent consumer of the original relative open-excision map. -/
open CategoryTheory Quillen.LocalCoefficients
universe u
example {X : Type u} [TopologicalSpace X] (U V : Set X) (A : System.{u, u} X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    QuasiIso (relativePushforwardChainMap (subspaceInclusion U)
      (intersectionInSubspace U V) V (fun _ hx ↦ hx) A) :=
  relativePushforwardChainMap_openExcision U V A hU hV hcover
