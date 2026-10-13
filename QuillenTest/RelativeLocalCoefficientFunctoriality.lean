/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
import Quillen.Topology.LocalCoefficients.RelativeFunctoriality
/-! Independent consumers of original relative spatial maps. -/
open CategoryTheory
universe u
open Quillen.LocalCoefficients
variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
example (f : C(X, Y)) (U : Set X) (V : Set Y) (h : Set.MapsTo f U V)
    (A : System.{u, u} Y) (e : ContinuousMap.HomotopyEquiv X Y) (he : e.toFun = f)
    (s : ContinuousMap.HomotopyEquiv U V) (hs : s.toFun = subspaceMap f U V h) :
    QuasiIso (relativePushforwardChainMap f U V h A) :=
  relativePushforwardChainMap_quasiIso_of_homotopyEquiv f U V h A e he s hs
