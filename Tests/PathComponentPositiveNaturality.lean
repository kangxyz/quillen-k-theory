/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quillen K-theory contributors
-/
module

public import Quillen.Topology.HomotopyGroups.PathComponentPositiveNaturality

/-! # Original component-map naturality consumers -/

@[expose] public section

noncomputable section

universe u v

open Quillen

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

example (f : C(X, Y)) (x : X) (y : Y) (p : Path (f x) y)
    (a : HomotopyGroup.Pi 0 (pathComponent x) ⟨x, mem_pathComponent_self x⟩) :
    homotopyGroupMap (pathComponentInclusion y) rfl
      (pathTransport (pathComponentMapBasepointPath f x y p) 0
        (homotopyGroupMap (pathComponentMap f x y ⟨p⟩) rfl a)) =
      pathTransport p 0 (homotopyGroupMap f rfl
        (homotopyGroupMap (pathComponentInclusion x) rfl a)) :=
  pathComponentMap_homotopyGroupMap_naturality f x y p 0 a

example (f : C(X, Y)) (x : X) (y : Y) (p : Path (f x) y) (n : ℕ) :
    (pathComponentPiMulEquiv y n).toMonoidHom.comp
      ((pathTransportMulEquiv (pathComponentMapBasepointPath f x y p) n).toMonoidHom.comp
        (piMap n (pathComponentMap f x y ⟨p⟩)
          (x := ⟨x, mem_pathComponent_self x⟩) rfl)) =
      ((pathTransportMulEquiv p n).toMonoidHom.comp (piMap n f (x := x) rfl)).comp
        (pathComponentPiMulEquiv x n).toMonoidHom :=
  pathComponentPiMulEquiv_naturality f x y p n
