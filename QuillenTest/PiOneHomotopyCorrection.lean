/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Quillen.Topology.HomotopyGroups.PathTransportFundamentalGroup
import Quillen.Topology.ClassifyingSpace.CompletionMapSurjectivity

/-! The actual correction permits distinct arbitrary endpoint paths in an abelian target. -/
universe u v
noncomputable section
open Quillen
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

example {f g : C(X, Y)} {x : X} {y : Y} (H : f.Homotopic g)
    (γ : Path (f x) y) (δ : Path (g x) y)
    (hc : ∀ a b : HomotopyGroup.Pi 1 Y y, a * b = b * a) :
    (pathTransportMulEquiv γ 0).toMonoidHom.comp (piMap 0 f rfl) =
      (pathTransportMulEquiv δ 0).toMonoidHom.comp (piMap 0 g rfl) :=
  piOne_homotopy_corrected H.some γ δ hc

example {f : C(X, Y)} {x : X} {y : Y}
    (γ δ : Path (f x) y) (hc : ∀ a b : HomotopyGroup.Pi 1 Y y, a * b = b * a) :
    (pathTransportMulEquiv γ 0).toMonoidHom.comp (piMap 0 f rfl) =
      (pathTransportMulEquiv δ 0).toMonoidHom.comp (piMap 0 f rfl) :=
  piOne_homotopy_corrected (ContinuousMap.Homotopy.refl f) γ δ hc

example {x y : X} (γ : Path x y) (a : HomotopyGroup.Pi 1 X x) :
    HomotopyGroup.pi1MulEquivFundamentalGroup (pathTransport γ 1 a) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath γ
        (HomotopyGroup.pi1MulEquivFundamentalGroup a) :=
  piOneEquivFundamentalGroup_pathTransport γ a
